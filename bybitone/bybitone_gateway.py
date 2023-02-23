import hashlib
import hmac
from pathlib import Path
import csv
import json
from collections import defaultdict
from datetime import datetime, timedelta
from time import time
from typing import Any, Dict, List, Callable
from urllib.parse import urlencode
from copy import copy
from peewee import chunked
from requests import ConnectionError

from vnpy.trader.database import database_manager
from vnpy.api.websocket import WebsocketClient
from vnpy.api.rest import Request, RestClient
from vnpy.trader.constant import (
    Exchange,
    Interval,
    OrderType,
    Product,
    Status,
    Direction,
    Offset
)
from vnpy.trader.object import (
    AccountData,
    BarData,
    TickData,
    OrderData,
    TradeData,
    ContractData,
    PositionData,
    HistoryRequest,
    SubscribeRequest,
    CancelRequest,
    OrderRequest
)
from vnpy.trader.event import EVENT_TIMER
from vnpy.trader.gateway import BaseGateway, LocalOrderManager
from vnpy.trader.utility import (save_connection_status,delete_dr_data,get_folder_path,load_json, save_json,remain_digit,get_symbol_mark,get_local_datetime,extract_vt_symbol,TZ_INFO,GetFilePath)
from vnpy.trader.setting import bybitone_account #导入账户字典

STATUS_BYBIT2VT = {
    "Created": Status.NOTTRADED,
    "New": Status.NOTTRADED,
    "PartiallyFilled": Status.PARTTRADED,
    "Filled": Status.ALLTRADED,
    "Cancelled": Status.CANCELLED,
    "PartiallyFilledCanceled": Status.CANCELLED,
    "Rejected": Status.REJECTED,
}

DIRECTION_VT2BYBIT = {Direction.LONG: "Buy", Direction.SHORT: "Sell"}
DIRECTION_BYBIT2VT = {v: k for k, v in DIRECTION_VT2BYBIT.items()}

OPPOSITE_DIRECTION = {
    Direction.LONG: Direction.SHORT,
    Direction.SHORT: Direction.LONG,
}

ORDER_TYPE_VT2BYBIT = {
    OrderType.LIMIT: "Limit",
    OrderType.MARKET: "Market",
}
ORDER_TYPE_BYBIT2VT = {v: k for k, v in ORDER_TYPE_VT2BYBIT.items()}

TIMEDELTA_MAP: Dict[Interval, timedelta] = {
    Interval.MINUTE: timedelta(minutes=1),
    Interval.HOUR: timedelta(hours=1),
    Interval.DAILY: timedelta(days=1),
}

INTERVAL_VT2BYBIT = {
    Interval.MINUTE: "1",
    Interval.HOUR: "60",
    Interval.DAILY: "D",
    Interval.WEEKLY: "W",
}

VT_SYMBOL_CATEGORY_MAP:Dict[str,str] = {}
CATEGORY_EXCHANGE_MAP:Dict[str,Exchange] = {
    "spot":Exchange.BYBITSPOT,
    "inverse":Exchange.BYBIT,
    "linear":Exchange.BYBIT,
    "option":Exchange.BYBIT
}

REST_HOST = "https://api.bybit.com"         # 主host  https://api.bybit.com备用host https://api.bytick.com
SPOT_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/spot"   #现货主网公共topic地址
USDT_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/linear"   #usdt,usdc合约主网公共topic地址
INVERSE_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/inverse"   #反向合约主网公共topic地址
OPTION_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/option"   #期权主网公共topic地址
PRIVATE_WS_HOST = "wss://stream.bybit.com/v5/private"  #主网私有topic地址

TESTNET_REST_HOST = "https://api-testnet.bybit.com"
TESTNET_SPOT_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/spot"   #现货主网公共topic地址
TESTNET_USDT_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/linear"   #usdt,usdc合约主网公共topic地址
TESTNET_INVERSE_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/inverse"   #反向合约主网公共topic地址
TESTNET_OPTION_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/option"   #期权主网公共topic地址
TESTNET_PRIVATE_WS_HOST = "wss://stream-testnet.bybit.com/v5/private"  #主网私有topic地址
#-------------------------------------------------------------------------------------------------   
class BybitOneGateway(BaseGateway):
    """
    BYBIT统一账户接口
    """
    #default_setting由vnpy.trader.ui.widget调用
    default_setting = {
        "ID": "",
        "Secret": "",
        "服务器": ["REAL", "TESTNET"],
        "代理地址": "",
        "代理端口": "",
    }

    exchanges = [Exchange.BYBIT,Exchange.BYBITSPOT]      #由main_engine add_gateway调用
    #所有合约列表
    recording_list = GetFilePath.recording_list
    #-------------------------------------------------------------------------------------------------   
    def __init__(self, event_engine):
        """
        """
        super().__init__(event_engine, "BYBITONE")
        self.orders: Dict[str, OrderData] = {}
        self.connect_time = datetime.now(TZ_INFO).strftime("%y%m%d%H%M%S")
        self.order_manager = LocalOrderManager(self, self.connect_time)
        self.ws_spot_data_api = BybitWebsocketDataApi(self)
        self.ws_usdt_data_api = BybitWebsocketDataApi(self)
        self.ws_inverse_data_api = BybitWebsocketDataApi(self)
        self.ws_option_data_api = BybitWebsocketDataApi(self)
        self.rest_api = BybitRestApi(self)
        self.ws_trade_api = BybitWebsocketTradeApi(self)

        self.count:int = 0
        self.recording_list = [vt_symbol for vt_symbol in self.recording_list if extract_vt_symbol(vt_symbol)[2] == self.gateway_name and not extract_vt_symbol(vt_symbol)[0].endswith("99")]
        #历史数据合约列表
        self.history_contracts = copy(self.recording_list)
        #rest查询合约列表
        self.query_contracts = [vt_symbol for vt_symbol in GetFilePath.all_trading_vt_symbols if extract_vt_symbol(vt_symbol)[2] == self.gateway_name and not extract_vt_symbol(vt_symbol)[0].endswith("99")]
        if not self.query_contracts:
            self.query_contracts = copy(self.recording_list)
    #-------------------------------------------------------------------------------------------------   
    def connect(self,log_account:dict = {}):
        """
        """
        if not log_account:
            log_account = bybitone_account
        key = log_account["APIKey"]
        secret = log_account["PrivateKey"]
        server = log_account["服务器"]
        proxy_host = log_account["代理地址"]
        proxy_port = log_account["代理端口"]
        proxy_type = log_account["proxy_type"]
        self.account_file_name = log_account["account_file_name"]
        self.rest_api.connect(key, secret, server, proxy_host, proxy_port,proxy_type)
        if server == "REAL":
            self.ws_spot_data_api.connect(SPOT_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
            self.ws_usdt_data_api.connect(USDT_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
            self.ws_inverse_data_api.connect(INVERSE_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
            self.ws_option_data_api.connect(OPTION_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
        else:
            self.ws_spot_data_api.connect(TESTNET_SPOT_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
            self.ws_usdt_data_api.connect(TESTNET_USDT_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
            self.ws_inverse_data_api.connect(TESTNET_INVERSE_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)
            self.ws_option_data_api.connect(TESTNET_OPTION_PUBLIC_WS_HOST,proxy_host, proxy_port,proxy_type)

        self.ws_trade_api.connect(key, secret, server, proxy_host, proxy_port,proxy_type)
        self.event_engine.register(EVENT_TIMER, self.process_timer_event)
        self.event_engine.register(EVENT_TIMER, self.query_history)
    #-------------------------------------------------------------------------------------------------   
    def subscribe(self, req: SubscribeRequest):
        """
        """
        symbol = req.symbol
        if symbol.endswith("-C") or symbol.endswith("-P"):
            self.ws_option_data_api.subscribe(req)
        elif symbol.endswith("PERP") or symbol.endswith("USDT"):
            self.ws_usdt_data_api.subscribe(req)
        else:
            self.ws_inverse_data_api.subscribe(req)
    #-------------------------------------------------------------------------------------------------   
    def send_order(self, req: OrderRequest):
        """
        """
        return self.rest_api.send_order(req)
    #-------------------------------------------------------------------------------------------------   
    def cancel_order(self, req: CancelRequest):
        """
        """
        self.rest_api.cancel_order(req)
    #-------------------------------------------------------------------------------------------------   
    def query_account(self):
        """
        """
        self.rest_api.query_account()
    #------------------------------------------------------------------------------------------------- 
    def query_order(self,vt_symbol:str):
        """
        查询未成交委托单
        """
        self.rest_api.query_active_order(vt_symbol)
    #------------------------------------------------------------------------------------------------- 
    def query_position(self,vt_symbol:str):
        """
        查询持仓
        """
        self.rest_api.query_position(vt_symbol)
    #-------------------------------------------------------------------------------------------------   
    def process_timer_event(self,event):
        """
        处理定时任务
        """
        self.query_account()
        if self.query_contracts and VT_SYMBOL_CATEGORY_MAP:
            vt_symbol = self.query_contracts.pop(0)
            self.query_order(vt_symbol)
            self.query_position(vt_symbol)
            self.query_contracts.append(vt_symbol)
        self.count += 1
        if self.count < 20:
            return
        self.count = 0
        self.ws_spot_data_api.send_packet({"op":"ping"})
        self.ws_usdt_data_api.send_packet({"op":"ping"})
        self.ws_inverse_data_api.send_packet({"op":"ping"})
        self.ws_option_data_api.send_packet({"op":"ping"})
        self.ws_trade_api.send_packet({"op":"ping"})
    #-------------------------------------------------------------------------------------------------   
    def query_history(self,event):
        """
        查询合约历史数据
        """
        if self.history_contracts and VT_SYMBOL_CATEGORY_MAP:
            vt_symbol = self.history_contracts.pop(0)
            symbol,exchange,gateway_name = extract_vt_symbol(vt_symbol)
            req = HistoryRequest(
                symbol = symbol,
                exchange = Exchange(exchange),
                interval = Interval.MINUTE,
                start = datetime.now(TZ_INFO) - timedelta(minutes = 200),
                gateway_name = self.gateway_name
            )
            self.rest_api.query_history(req)
            self.rest_api.set_leverage(vt_symbol)
    #---------------------------------------------------------------------------------------
    def on_order(self, order: OrderData) -> None:
        """
        收到委托单推送，BaseGateway推送数据
        """
        self.orders[order.vt_orderid] = copy(order)
        super().on_order(order)
    #---------------------------------------------------------------------------------------
    def get_order(self, vt_orderid: str) -> OrderData:
        """
        用vt_orderid获取委托单数据
        """
        return self.orders.get(vt_orderid, None)
    #-------------------------------------------------------------------------------------------------   
    def close(self):
        """
        """
        self.rest_api.stop()
        self.ws_spot_data_api.stop()
        self.ws_usdt_data_api.stop()
        self.ws_inverse_data_api.stop()
        self.ws_option_data_api.stop()
        self.ws_trade_api.stop()
#-------------------------------------------------------------------------------------------------   
class BybitRestApi(RestClient):
    """
    ByBit REST API
    """
    #-------------------------------------------------------------------------------------------------   
    def __init__(self, gateway: BybitOneGateway):
        """
        """
        super().__init__()
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        self.order_manager = gateway.order_manager
        self.key = ""
        self.secret = b""
        self.account_date = None    #账户日期
        self.accounts_info:Dict[str,dict] = {}
    #-------------------------------------------------------------------------------------------------   
    def get_server_time(self):
        """
        获取服务器时间
        """
        self.add_request(
            "GET",
            "/v3/public/time",
            callback=self.on_server_time,
            )
    #-------------------------------------------------------------------------------------------------   
    def on_server_time(self,data: dict, request: Request):
        """
        收到服务器时间回报
        """
        server_time = get_local_datetime(int(data["result"]["timeNano"]))
        local_time = datetime.now(TZ_INFO)
        self.gateway.write_log(f"服务器时间：{server_time}，本地时间：{local_time}")
    #-------------------------------------------------------------------------------------------------   
    def sign(self, request: Request):
        """
        Generate ByBit signature.
        """
        if request.method == "GET":
            api_params = request.params
            if not api_params:
                api_params = request.params = {}
            else:
                api_params = urlencode(api_params)
        else:
            api_params = request.data
            if not api_params:
                api_params = request.data = {}
            else:
                api_params = json.dumps(api_params)
                request.data = api_params

        recv_window = str(30 * 1000)
        nonce = generate_timestamp(-20)
        if not api_params:
            if request.method == "GET":
                api_params = ""
            else:
                api_params = request.data = json.dumps({})
        param_str= str(nonce) + self.key + recv_window + api_params
        signature = hmac.new(self.secret, param_str.encode("utf-8"),hashlib.sha256).hexdigest()
        if request.headers is None:
            request.headers = {"Content-Type": "application/json"}
        request.headers["X-BAPI-API-KEY"] = self.key
        request.headers["X-BAPI-SIGN"] = signature
        request.headers["X-BAPI-TIMESTAMP"] = str(nonce)
        request.headers["X-BAPI-RECV-WINDOW"] = recv_window
        return request
    #-------------------------------------------------------------------------------------------------   
    def connect(
        self,
        key: str,
        secret: str,
        server: str,
        proxy_host: str,
        proxy_port: int,
        proxy_type:str,
    ):
        """
        Initialize connection to REST server.
        """
        self.key = key
        self.secret = secret.encode()
        if server == "REAL":
            self.init(REST_HOST, proxy_host, proxy_port,proxy_type,gateway_name = self.gateway_name)
        else:
            self.init(TESTNET_REST_HOST, proxy_host, proxy_port,proxy_type,gateway_name = self.gateway_name)

        self.start(3)
        self.gateway.write_log(f"交易接口:{self.gateway_name},REST API启动成功")
        self.get_server_time()
        self.query_contract()
    #------------------------------------------------------------------------------------------------- 
    def get_category(self,vt_symbol:str):
        """
        通过vt_symbol获取产品类型
        """
        category = VT_SYMBOL_CATEGORY_MAP.get(vt_symbol, None)
        # 产品类型缺失处理
        if not category:
            symbol,*_ = extract_vt_symbol(vt_symbol)
            if symbol.endswith("USDT") or symbol.endswith("PERP"):
                category = "linear"
            else:
                category = "inverse"
        return category
    #-------------------------------------------------------------------------------------------------  
    def set_leverage(self,vt_symbol:str):
        """
        设置合约杠杆
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        category = self.get_category(vt_symbol)
        path = "/v5/position/set-leverage"
        data = {"category":category,"symbol":symbol,"buyLeverage":20,"sellLeverage":20}
        self.add_request("POST", path,self.on_leverage,data = data,extra=data)
    #-------------------------------------------------------------------------------------------------   
    def on_leverage(self, data: dict, request: Request):
        """
        收到设置杠杆回调
        """
        pass
    #-------------------------------------------------------------------------------------------------   
    def send_order(self, req: OrderRequest):
        """
        """
        orderId = req.symbol + "-" + self.order_manager.new_local_orderid()
        data = {
            "category":self.get_category(req.vt_symbol),
            "symbol": req.symbol,
            "price":str(req.price),
            "qty": str(req.volume),
            "side": DIRECTION_VT2BYBIT[req.direction],
            "orderType":ORDER_TYPE_VT2BYBIT[req.type],
            "orderLinkId": orderId,
            "positionIdx":"0",              #单向持仓
            "timeInForce": "GTC",
        }
        #平仓信号仅减仓
        if req.offset == Offset.CLOSE:
            data["reduceOnly"] = True
            data["closeOnTrigger"] = True
        order = req.create_order_data(orderId, self.gateway_name)
        order.datetime = datetime.now(TZ_INFO)

        self.add_request(
            "POST",
            "/v5/order/create",
            callback=self.on_send_order,
            data=data,
            extra=order,
            on_failed=self.on_send_order_failed,
            on_error=self.on_send_order_error,
        )

        self.order_manager.on_order(order)
        return order.vt_orderid
    #-------------------------------------------------------------------------------------------------   
    def on_send_order_failed(self, status_code, request: Request):
        """
        Callback when sending order failed on server.
        """
        order = request.extra
        order.status = Status.REJECTED
        self.order_manager.on_order(order)
        data = request.response.json()
        if not data:
            return
        error_msg = data["retMsg"]
        error_code = data["retCode"]
        msg = f"发送委托失败，错误代码:{error_code},  错误信息：{error_msg}，委托单数据：{order}"
        self.gateway.write_log(msg)
    #-------------------------------------------------------------------------------------------------   
    def on_send_order_error(
        self, exception_type: type, exception_value: Exception, tracebacks, request: Request
    ):
        """
        Callback when sending order caused exception.
        """
        order:OrderData = request.extra
        order.status = Status.REJECTED
        self.order_manager.on_order(order)

        # Record exception if not ConnectionError
        if not issubclass(exception_type, ConnectionError):
            self.on_error(exception_type, exception_value, tracebacks, request)
    #-------------------------------------------------------------------------------------------------   
    def on_send_order(self, data: dict, request: Request):
        """
        """
        if self.check_error("发送委托", data):
            order:OrderData = request.extra
            order.status = Status.REJECTED
            self.order_manager.on_order(order)
            self.gateway.write_log(f"错误委托单：{order}")
            return
        orderLinkId = request.extra.orderid
        result = data["result"]
        self.order_manager.update_orderid_map(
            orderLinkId,
            result["orderId"]
        )
    #-------------------------------------------------------------------------------------------------   
    def cancel_order(self, req: CancelRequest):
        """
        """
        order: OrderData = self.gateway.get_order(req.vt_orderid)
        sys_orderid = self.order_manager.get_sys_orderid(req.orderid)
        
        data = {
            "category":self.get_category(req.vt_symbol),
            "orderId": sys_orderid,
            "symbol": req.symbol,
        }

        self.add_request(
            "POST",
            path="/v5/order/cancel",
            data=data,
            callback=self.on_cancel_order,
            on_failed=self.on_cancel_failed,
            extra=order
        )
    #-------------------------------------------------------------------------------------------------   
    def on_cancel_order(self, data: dict, request: Request):
        """
        """
        if self.check_error("取消委托", data):
            error_code = data["retCode"]
            # 重复撤销委托单被拒推送
            if error_code == 110001:
                order: OrderData= request.extra
                order.status = Status.REJECTED
                self.order_manager.on_order(order)
            return
    #---------------------------------------------------------------------------------------
    def on_cancel_failed(self, status_code, request: Request) -> None:
        """
        收到取消委托单失败回报
        """
        if request.extra:
            order = request.extra
            order.status = Status.REJECTED
            self.gateway.on_order(order)

        msg = f"撤单失败，状态码：{status_code}，错误信息：{request.response.text}"
        self.gateway.write_log(msg)
    #-------------------------------------------------------------------------------------------------   
    def query_contract(self):
        """
        """
        params = [{"category":"linear"},{"category":"inverse"},{"category":"spot"}]
        for param in params:
            param.update({"limit":1000})
            self.add_request( "GET", "/v5/market/instruments-info", self.on_query_contract,param)
    #-------------------------------------------------------------------------------------------------   
    def check_error(self, name: str, data: dict):
        """
        """
        if data["retCode"]:
            error_code = data["retCode"]
            error_msg = data["retMsg"]
            msg = f"{name}失败，错误代码：{error_code}，信息：{error_msg}"
            self.gateway.write_log(msg)
            return True

        return False
    #-------------------------------------------------------------------------------------------------   
    def on_query_contract(self, data: dict, request: Request):
        """
        查询合约
        """
        if self.check_error("查询合约", data):
            return
        category = data["result"]["category"]
        if category == "option":
            product = Product.OPTION
        elif category == "spot":
            product = Product.SPOT
        else:
            product = Product.FUTURES
        for contract_data in data["result"]["list"]:
            contract = ContractData(
                symbol=contract_data["symbol"],
                exchange=CATEGORY_EXCHANGE_MAP[category],
                name=contract_data["symbol"],
                product=product,
                size = 20,             #合约杠杆
                price_tick=float(contract_data["priceFilter"].get("minPrice",contract_data["priceFilter"]["tickSize"])),
                max_volume = float(contract_data["lotSizeFilter"]["maxOrderQty"]),
                min_volume=float(contract_data["lotSizeFilter"]["minOrderQty"]),
                gateway_name=self.gateway_name
            )
            VT_SYMBOL_CATEGORY_MAP[contract.vt_symbol] = category
            self.gateway.on_contract(contract)
        self.gateway.write_log(f"{self.gateway_name}，{category.upper()}合约信息查询成功")
    #-------------------------------------------------------------------------------------------------  
    def query_account(self):
        """
        发送查询资金请求
        """
        params = [{"accountType":"UNIFIED"},{"accountType":"CONTRACT"}]
        for param in params:
             self.add_request(method ="GET", path = "/v5/account/wallet-balance", callback = self.on_query_account,params = param)
    #------------------------------------------------------------------------------------------------- 
    def on_query_account(self,data: dict, request: Request):
        """
        收到资金回报
        """
        if data["retCode"] == 10016:
            return
        if not data["result"]:
            return
        data = data["result"]["list"][0]
        for account_data in data["coin"]:
            coin = account_data["coin"]
            account = AccountData(
                accountid= f"{coin}_{self.gateway_name}",
                balance= float(account_data["walletBalance"]),
                available = float(account_data["availableToWithdraw"]),
                margin = float(account_data["totalPositionIM"]) if account_data["totalPositionIM"] else 0,
                position_profit = float(account_data["unrealisedPnl"]) if account_data["unrealisedPnl"] else 0,
                close_profit = float(account_data["cumRealisedPnl"]) if account_data["cumRealisedPnl"] else 0,
                datetime = datetime.now(TZ_INFO),
                gateway_name= self.gateway_name
            )
            if account.balance:
                self.gateway.on_account(account)
                #保存账户资金信息
                self.accounts_info[account.accountid] = account.__dict__
        if  not self.accounts_info:
            return
        accounts_info = list(self.accounts_info.values())
        account_date = accounts_info[-1]["datetime"].date()
        account_path = GetFilePath().ctp_account_path.replace("ctp_account_1",self.gateway.account_file_name)
        for account_data in accounts_info:
            if not Path(account_path).exists(): # 如果文件不存在，需要写header
                with open(account_path, 'w',newline="") as f1:          #newline=""不自动换行
                    w1 = csv.DictWriter(f1, account_data.keys())
                    w1.writeheader()
                    w1.writerow(account_data)
            else: # 文件存在，不需要写header
                if self.account_date and self.account_date != account_date:        #一天写入一次账户信息         
                    with open(account_path,'a',newline="") as f1:                               #a二进制追加形式写入
                        w1 = csv.DictWriter(f1, account_data.keys())
                        w1.writerow(account_data)
        self.account_date = account_date
    #-------------------------------------------------------------------------------------------------   
    def query_position(self,vt_symbol:str):
        """
        发送查询持仓请求
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        params={
            "category":self.get_category(vt_symbol),
            "limit":50,
            "symbol":symbol
        }
        if params["category"] == "inverse":
            path = "/contract/v3/private/position/list"
        else:
            path = "/v5/position/list"
        self.add_request(method = "GET", path = path, callback = self.on_query_position,params = params)
    #-------------------------------------------------------------------------------------------------   
    def on_query_position(self, data: dict, request: Request):
        """
        收到持仓回报
        """
        if self.check_error("查询持仓", data):
            if data["retCode"] == 10001:
                delete_dr_data(request.params["symbol"],self.gateway_name)
            elif data["retCode"] == 10002:
                # 服务器时间与本地时间不同步，重启交易子进程
                save_connection_status(self.gateway_name,False)
            return
        category = data["result"]["category"]
        exchange = CATEGORY_EXCHANGE_MAP[category]
        raw_data = data["result"]["list"]
        for pos_data in raw_data:
            if category == "inverse":
                price = float(pos_data["entryPrice"])
            else:
                price = float(pos_data["avgPrice"])
            direction = DIRECTION_BYBIT2VT.get(pos_data["side"],None)
            if direction:
                pos = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=direction,
                    volume=abs(float(pos_data["size"])),
                    price=price,  
                    pnl = float(pos_data["unrealisedPnl"]),              #持仓盈亏
                    gateway_name=self.gateway_name
                )
                self.gateway.on_position(pos)
            else:
                long_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.LONG,
                    volume = 0,
                    price = 0,
                    pnl = 0,
                    frozen = 0,
                    gateway_name=self.gateway_name,
                    )
                short_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.SHORT,
                    volume = 0,
                    price = 0,
                    pnl = 0,
                    frozen = 0,
                    gateway_name=self.gateway_name,
                    )
                self.gateway.on_position(long_position)
                self.gateway.on_position(short_position)
    #-------------------------------------------------------------------------------------------------   
    def query_active_order(self,vt_symbol:str):
        """
        发送查询活动委托单请求
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        params = {
            "category":self.get_category(vt_symbol),
            "limit": 20,
            "symbol":symbol,
        }
        if params["category"] == "inverse":
            path = "/contract/v3/private/order/unfilled-orders"
        else:
            path = "/v5/order/realtime"
        self.add_request( "GET", path, callback=self.on_query_order, params=params )
    #-------------------------------------------------------------------------------------------------   
    def on_query_order(self, data: dict, request: Request):
        """
        收到活动委托单回报
        """
        if self.check_error("查询未成交委托", data):
            if data["retCode"] == "10001":
                delete_dr_data(request.params["symbol"],self.gateway_name)
            return
        result = data["result"]["list"]
        if not result:
            return
        category = data["result"]["category"]
        exchange = CATEGORY_EXCHANGE_MAP[category]
        for order_data in result:
            status = STATUS_BYBIT2VT[order_data["orderStatus"]]
            sys_orderid = order_data["orderId"]
            order = self.order_manager.get_order_with_sys_orderid(sys_orderid)
            if order:
                order.traded = float(order_data["cumExecQty"])
                order.status = status
            else:
                # Use sys_orderid as local_orderid when
                # order placed from other source
                local_orderid = order_data["orderLinkId"]
                order_datetime = get_local_datetime(int(order_data["createdTime"]))
                if not local_orderid:
                    local_orderid = sys_orderid

                self.order_manager.update_orderid_map(
                    local_orderid,
                    sys_orderid
                )

                order = OrderData(
                    symbol=order_data["symbol"],
                    exchange=exchange,
                    orderid=local_orderid,
                    type=ORDER_TYPE_BYBIT2VT[order_data["orderType"]],
                    direction=DIRECTION_BYBIT2VT[order_data["side"]],
                    price=float(order_data["price"]),
                    volume=float(order_data["qty"]),
                    traded=float(order_data["cumExecQty"]),
                    status=status,
                    datetime= order_datetime,
                    gateway_name=self.gateway_name
                )
            if order_data["reduceOnly"]:
                order.offset = Offset.CLOSE
            self.order_manager.on_order(order)
    #-------------------------------------------------------------------------------------------------   
    def query_history(self, req: HistoryRequest) -> List[BarData]:
        """
        查询历史数据
        """
        history = []
        count = 200
        start_time = int(req.start.timestamp())
        time_consuming_start = time()
        while True:
            end_time = get_local_datetime(start_time,8) + timedelta(minutes=200)
            # Create query params
            params = {
                "category":self.get_category(req.vt_symbol),
                "symbol": req.symbol,
                "interval": INTERVAL_VT2BYBIT[req.interval],
                "start": start_time * 1000,
                "end":  int(end_time.timestamp()) * 1000,
                "limit": count
            }
            # Get response from server
            resp = self.request(
                "GET",
                "/v5/market/kline",
                params=params
            )
            # Break if request failed with other status code
            if not resp:
                msg = f"合约：{req.vt_symbol}，获取历史数据失败"
                self.gateway.write_log(msg)
                continue
            elif resp.status_code // 100 != 2:
                msg = f"合约：{req.vt_symbol}，获取历史数据失败，状态码：{resp.status_code}，信息：{resp.text}"
                self.gateway.write_log(msg)
                continue
            else:
                data = resp.json()
                if not data:
                    msg = f"获取合约：{req.vt_symbol}历史数据为空"
                    self.gateway.write_log(msg)
                    break
                elif data["retCode"] == 10001 or not data["result"]:
                    delete_dr_data(req.symbol,self.gateway_name)
                    msg = f"无法获取合约：{req.vt_symbol}历史数据"
                    self.gateway.write_log(msg)
                    break
                buf = []
                for data in data["result"]["list"]:
                    dt = get_local_datetime(int(data[0]))
                    bar = BarData(
                        symbol=req.symbol,
                        exchange=req.exchange,
                        datetime=dt,
                        interval=req.interval,
                        volume=float(data[5]),
                        open_price=float(data[1]),
                        high_price=float(data[2]),
                        low_price=float(data[3]),
                        close_price=float(data[4]),
                        gateway_name=self.gateway_name
                    )
                    buf.append(bar)
                history.extend(buf)
                # 收集超过200根bar退出循环
                if len(history) >= 200:
                    break
                # Update start time
                start_time = int((datetime.fromtimestamp(start_time) - timedelta(minutes= 200)).timestamp())

        if not history:
            msg = f"未获取到合约：{req.vt_symbol}历史数据"
            self.gateway.write_log(msg)
            return
        for bar_data in chunked(history, 10000):               #分批保存数据
            try:
                database_manager.save_bar_data(bar_data,False)      #保存数据到数据库  
            except Exception as err:
                self.gateway.write_log(f"{err}")
                return
        time_consuming_end =time()        
        query_time = round(time_consuming_end - time_consuming_start,3)
        msg = f"载入{req.vt_symbol}:bar数据，开始时间：{history[-1].datetime} ，结束时间： {history[0].datetime}，数据量：{len(history)}，耗时:{query_time}秒"
        self.gateway.write_log(msg)
#-------------------------------------------------------------------------------------------------   
class BybitWebsocketDataApi(WebsocketClient):
    """
    """

    def __init__(self, gateway: BybitOneGateway):
        """
        """
        super().__init__()

        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        # 产品类型
        self.category: str = ""

        self.callbacks: Dict[str, Callable] = {}
        self.ticks: Dict[str, TickData] = {}
        self.subscribed: Dict[str, SubscribeRequest] = {}

        self.order_book_bids = defaultdict(dict)       #订单簿买单字典
        self.order_book_asks = defaultdict(dict)       #订单簿卖单字典
    #-------------------------------------------------------------------------------------------------   
    def connect(
        self, url: str, proxy_host: str, proxy_port: int,proxy_type:str
    ):
        """
        """
        self.proxy_host = proxy_host
        self.proxy_port = proxy_port
        self.category = url.split('/')[-1].upper()
        
        self.init(url, self.proxy_host, self.proxy_port,proxy_type,gateway_name = self.gateway_name)
        self.start()
    #-------------------------------------------------------------------------------------------------   
    def subscribe(self, req: SubscribeRequest):
        """
        Subscribe to tick data update.
        """
        self.subscribed[req.vt_symbol] = req

        tick = TickData(
            symbol=req.symbol,
            exchange=req.exchange,
            datetime=datetime.now(TZ_INFO),
            name=req.symbol,
            gateway_name=self.gateway_name
        )
        self.ticks[req.symbol] = tick
        # 订阅tick行情
        self.subscribe_topic(f"tickers.{req.symbol}", self.on_tick)
        # 订阅1档orderbook深度
        self.subscribe_topic(f"orderbook.1.{req.symbol}", self.on_depth)
        # 订阅成交数据
        self.subscribe_topic(f"publicTrade.{req.symbol}", self.on_public_trade)
    #-------------------------------------------------------------------------------------------------   
    def subscribe_topic(self, topic: str, callback: Callable[[str, dict], Any]):
        """
        订阅私有主题
        """
        self.callbacks[topic] = callback

        req = {
            "op": "subscribe",
            "args": [topic],
        }
        self.send_packet(req)
    #-------------------------------------------------------------------------------------------------   
    def on_connected(self):
        """
        """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API {self.category}行情连接成功")
        for req in list(self.subscribed.values()):
            self.subscribe(req)
    #-------------------------------------------------------------------------------------------------   
    def on_disconnected(self):
        """
        """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API {self.category}行情连接断开")
    #-------------------------------------------------------------------------------------------------   
    def on_packet(self, packet: dict):
        """
        """
        # 过滤心跳回报
        if packet.get("op", None) in ["ping","pong"]:
            return
        if "topic" in packet:
            channel = packet["topic"]
            callback = self.callbacks[channel]
            callback(packet)
        else:
            if not packet["success"]:
                ret_msg = packet["ret_msg"]
                # 过滤重复订阅错误回报
                if "already subscribed" in ret_msg:
                    return
                self.gateway.write_log(f"交易接口：{self.gateway_name}，Websocket API出错，错误信息：{ret_msg}")
    #-------------------------------------------------------------------------------------------------   
    def on_tick(self, packet: dict):
        """
        * 收到tick行情回报
        """
        topic = packet["topic"]
        type_ = packet["type"]
        data = packet["data"]
        timestamp = packet["ts"]
        symbol = topic.replace("tickers.", "")
        tick = self.ticks[symbol]
        # 收到快照数据推送
        if type_ == "snapshot":
            tick.high_price = float(data["highPrice24h"])
            tick.low_price = float(data["lowPrice24h"])
            tick.pre_close = float(data["prevPrice24h"])
            tick.open_interest = float(data["openInterest"])
            tick.last_price = float(data["lastPrice"])
            tick.volume = float(data["volume24h"])

        # snapshot和delta都推送的数据
        tick.bid_price_1 = float(data["bid1Price"])
        tick.bid_volume_1 = float(data["bid1Size"])
        tick.ask_price_1 = float(data["ask1Price"])
        tick.ask_volume_1 = float(data["ask1Size"])

        tick.datetime = get_local_datetime(int(timestamp))
    #-------------------------------------------------------------------------------------------------   
    def on_depth(self, packet: dict):
        """
        """
        data = packet["data"]
        type_ = packet["type"]

        # 更新深度数据到bids，asks
        symbol = data["s"]
        tick = self.ticks[symbol]
        tick.datetime = get_local_datetime(int(packet["ts"]))
        bids = data["b"]
        asks = data["a"]
        #全量推送
        if type_ == "snapshot":
            self.order_book_bids[tick.vt_symbol].clear()
            self.order_book_asks[tick.vt_symbol].clear()

        #更新order_books并删除委托量为0的价格缓存
        for bid_data in bids:
            self.order_book_bids[tick.vt_symbol].update({bid_data[0]:bid_data[1]})
            if not float(bid_data[1]):
                del self.order_book_bids[tick.vt_symbol][bid_data[0]]
        for ask_data in asks:
            self.order_book_asks[tick.vt_symbol].update({ask_data[0]:ask_data[1]})   
            if not float(ask_data[1]):
                del self.order_book_asks[tick.vt_symbol][ask_data[0]]
        sort_bids = sorted(self.order_book_bids[tick.vt_symbol].items(), key=lambda x:float(x[0]),reverse=True)[:5]    #买单价格从高到低排序
        sort_asks = sorted(self.order_book_asks[tick.vt_symbol].items(), key=lambda x:float(x[0]),reverse=False)[:5]   #卖单价格从低到高排序
        for n,buf in enumerate(sort_bids):
            tick.__setattr__(f"bid_price_{(n + 1)}", float(buf[0]))
            tick.__setattr__(f"bid_volume_{(n + 1)}", float(buf[1]))
        for n,buf in enumerate(sort_asks):
            tick.__setattr__(f"ask_price_{(n + 1)}" , float(buf[0]))
            tick.__setattr__(f"ask_volume_{(n + 1)}", float(buf[1]))

        if tick.last_price:
            self.gateway.on_tick(copy(tick))
    #-------------------------------------------------------------------------------------------------
    def on_public_trade(self,packet:dict):
        """
        收到平台成交回报
        """
        data = packet["data"]
        for trade_data in data:
            symbol = trade_data["s"]
            tick = self.ticks[symbol]
            tick.last_price = float(trade_data["p"])
            tick.datetime = get_local_datetime(trade_data["T"])
            self.gateway.on_tick(copy(tick))
#-------------------------------------------------------------------------------------------------   
class BybitWebsocketTradeApi(WebsocketClient):
    def __init__(self, gateway: BybitOneGateway):
        """
        """
        super().__init__()
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        self.order_manager = gateway.order_manager

        self.key = ""
        self.secret = b""
        self.callbacks: Dict[str, Callable] = {}
    #-------------------------------------------------------------------------------------------------   
    def connect(
        self, key: str, secret: str, server: str, proxy_host: str, proxy_port: int,proxy_type:str,
    ):
        """
        """
        self.key = key
        self.secret = secret.encode()
        self.proxy_host = proxy_host
        self.proxy_port = proxy_port
        self.server = server

        if self.server == "REAL":
            url =  PRIVATE_WS_HOST
        else:
            url = TESTNET_PRIVATE_WS_HOST

        self.init(url, self.proxy_host, self.proxy_port,proxy_type,gateway_name = self.gateway_name)
        self.start()
    #-------------------------------------------------------------------------------------------------   
    def login(self):
        """
        """
        expires = generate_timestamp(20)
        msg = f"GET/realtime{int(expires)}"
        signature = sign(self.secret, msg.encode())

        req = {
            "op": "auth",
            "args": [self.key, expires, signature]
        }
        self.send_packet(req)
    #-------------------------------------------------------------------------------------------------   
    def on_login(self):
        """
        收到登录回报
        """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API登录成功")
        self.subscribe_topic("order", self.on_order)
        self.subscribe_topic("execution", self.on_trade)
        self.subscribe_topic("position", self.on_position)
    #-------------------------------------------------------------------------------------------------   
    def subscribe_topic(self, topic: str, callback: Callable[[str, dict], Any]):
        """
        Subscribe to all private topics.
        """
        self.callbacks[topic] = callback

        req = {
            "op": "subscribe",
            "args": [topic],
        }
        self.send_packet(req)
    #-------------------------------------------------------------------------------------------------   
    def on_packet(self, packet: dict):
        """
        """
        # 过滤pong回报
        if packet.get("op", None) == "pong":
            return

        if "topic" not in packet:
            # 签名成功后调用on_login
            if packet["success"] and packet["op"] == "auth":
                self.on_login()
        else:
            channel = packet["topic"]            
            callback = self.callbacks[channel]
            callback(packet)
    #-------------------------------------------------------------------------------------------------   
    def on_connected(self):
        """
        """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API交易连接成功")
        self.login()
    #-------------------------------------------------------------------------------------------------   
    def on_disconnected(self):
        """
        """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API交易连接断开")
    #-------------------------------------------------------------------------------------------------   
    def on_trade(self, packet):
        """
        """
        for trade_data in packet["data"]:
            category = trade_data["category"]
            exchange = CATEGORY_EXCHANGE_MAP[category]
            orderId = trade_data.get("orderLinkId",None)
            if not orderId:
                orderId = trade_data["orderId"]
            trade_datetime = get_local_datetime(int(trade_data["execTime"]))        
            trade = TradeData(
                symbol=trade_data["symbol"],
                exchange=exchange,
                orderid=orderId,
                tradeid=trade_data["execId"],
                direction=DIRECTION_BYBIT2VT[trade_data["side"]],
                price=float(trade_data["execPrice"]),
                volume=float(trade_data["execQty"]),
                datetime =trade_datetime,
                gateway_name=self.gateway_name,
            )
            self.gateway.on_trade(trade)
    #-------------------------------------------------------------------------------------------------   
    def on_order(self, packet):
        """
        """
        for order_data in packet["data"]:
            category = order_data["category"]
            exchange = CATEGORY_EXCHANGE_MAP[category]
            sys_orderid = order_data["orderId"]
            order = self.order_manager.get_order_with_sys_orderid(sys_orderid)

            if order:
                order.traded = float(order_data["cumExecQty"])
                order.status = STATUS_BYBIT2VT[order_data["orderStatus"]]
            else:
                # Use sys_orderid as local_orderid when
                # order placed from other source
                local_orderid = order_data["orderLinkId"]
                order_datetime = get_local_datetime(int(order_data["createdTime"]))
                if not local_orderid:
                    local_orderid = sys_orderid

                self.order_manager.update_orderid_map(
                    local_orderid,
                    sys_orderid
                )

                order = OrderData(
                    symbol=order_data["symbol"],
                    exchange=exchange,
                    orderid=local_orderid,
                    type=ORDER_TYPE_BYBIT2VT[order_data["orderType"]],
                    direction=DIRECTION_BYBIT2VT[order_data["side"]],
                    price=float(order_data["price"]),
                    volume=float(order_data["qty"]),
                    traded=float(order_data["cumExecQty"]),
                    status=STATUS_BYBIT2VT[order_data["orderStatus"]],
                    datetime= order_datetime,
                    gateway_name=self.gateway_name
                )
            if order_data["reduceOnly"]:
                order.offset = Offset.CLOSE
            self.order_manager.on_order(order)
    #-------------------------------------------------------------------------------------------------   
    def on_position(self, packet):
        """
        收到持仓回报
        """
        for pos_data in packet["data"]:
            # 通过杠杆区分现货，合约
            if pos_data["leverage"] == "20":
                exchange = Exchange.BYBIT
            else:
                exchange = Exchange.BYBITSPOT
            direction = DIRECTION_BYBIT2VT.get(pos_data["side"],None)
            if direction:
                pos = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=direction,
                    volume=abs(float(pos_data["size"])),
                    price=float(pos_data["entryPrice"]),
                    pnl = float(pos_data["unrealisedPnl"]),
                    gateway_name=self.gateway_name
                )   
                self.gateway.on_position(pos)
            else:
                long_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.LONG,
                    volume = 0,
                    price = 0,
                    pnl = 0,
                    frozen = 0,
                    gateway_name=self.gateway_name,
                    )
                short_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.SHORT,
                    volume = 0,
                    price = 0,
                    pnl = 0,
                    frozen = 0,
                    gateway_name=self.gateway_name,
                    )
                self.gateway.on_position(long_position)
                self.gateway.on_position(short_position)
#-------------------------------------------------------------------------------------------------   
def generate_timestamp(expire_after: float = 30) -> int:
    """
    :param expire_after: expires in seconds.
    :return: timestamp in milliseconds
    """
    return int(time() * 1000 + expire_after * 1000)
#-------------------------------------------------------------------------------------------------   
def sign(secret: bytes, data: bytes) -> str:
    """
    secret签名
    """
    return hmac.new(
        secret, data, digestmod=hashlib.sha256
    ).hexdigest()
