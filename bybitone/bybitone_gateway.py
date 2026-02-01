import csv
import hashlib
import hmac
import json
from collections import defaultdict
from copy import copy
from datetime import datetime, timedelta
from pathlib import Path
from threading import Lock
from time import time,sleep
from typing import Any, Callable, Dict, List
from urllib.parse import urlencode

from peewee import chunked
from requests import ConnectionError
from vnpy.api.rest import Request, RestClient
from vnpy.api.websocket import WebsocketClient
from vnpy.trader.constant import (
    Direction,
    Exchange,
    Interval,
    Offset,
    OrderType,
    Product,
    Status,
)
from vnpy.trader.database import database_manager
from vnpy.trader.event import EVENT_TIMER
from vnpy.trader.gateway import BaseGateway, LocalOrderManager
from vnpy.trader.object import (
    AccountData,
    BarData,
    CancelRequest,
    ContractData,
    HistoryRequest,
    OrderData,
    OrderRequest,
    PositionData,
    SubscribeRequest,
    TickData,
    TradeData,
)
from vnpy.trader.setting import bybitone_account  # 导入账户字典
from vnpy.trader.utility import (
    TZ_INFO,
    GetFilePath,
    delete_dr_data,
    extract_vt_symbol,
    get_folder_path,
    get_local_datetime,
    get_symbol_mark,
    is_target_contract,
    load_json,
    remain_digit,
    save_connection_status,
    save_json,
)

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
    OrderType.FAK: "Market",
    OrderType.FOK: "Market",
}

TIMEINFORCE_MAP = {
    OrderType.LIMIT:"GTC",
    OrderType.FAK:"IOC",
    OrderType.FOK:"FOK",

}

ORDER_TYPE_BYBIT2VT = {v: k for k, v in TIMEINFORCE_MAP.items()}

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
CATEGORY_EXCHANGE_MAP: Dict[str, Exchange] = {"spot": Exchange.BYBITSPOT, "inverse": Exchange.BYBIT, "linear": Exchange.BYBIT, "option": Exchange.BYBIT}
CATEGORY_PRODUCT_MAP: Dict[str, Product] = {"spot": Product.SPOT, "inverse": Product.FUTURES, "linear":  Product.FUTURES, "option":  Product.OPTION}
REST_HOST = "https://api.bybit.com"  # 主host  https://api.bybit.com备用host https://api.bytick.com
SPOT_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/spot"  # 现货主网公共topic地址
USDT_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/linear"  # usdt,usdc合约主网公共topic地址
INVERSE_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/inverse"  # 反向合约主网公共topic地址
OPTION_PUBLIC_WS_HOST = "wss://stream.bybit.com/v5/public/option"  # 期权主网公共topic地址
PRIVATE_WS_HOST = "wss://stream.bybit.com/v5/private"  # 主网私有topic地址

TESTNET_REST_HOST = "https://api-testnet.bybit.com"
TESTNET_SPOT_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/spot"  # 现货主网公共topic地址
TESTNET_USDT_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/linear"  # usdt,usdc合约主网公共topic地址
TESTNET_INVERSE_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/inverse"  # 反向合约主网公共topic地址
TESTNET_OPTION_PUBLIC_WS_HOST = "wss://stream-testnet.bybit.com/v5/public/option"  # 期权主网公共topic地址
TESTNET_PRIVATE_WS_HOST = "wss://stream-testnet.bybit.com/v5/private"  # 主网私有topic地址
# ----------------------------------------------------------------------------------------------------
class BybitOneGateway(BaseGateway):
    """
    * BYBIT统一账户接口
    * 只支持单向持仓
    """

    # default_setting由vnpy.trader.ui.widget调用
    default_setting = {
        "ID": "",
        "Secret": "",
        "server": ["REAL", "TESTNET"],
        "host": "",
        "port": "",
    }

    exchanges = [Exchange.BYBIT, Exchange.BYBITSPOT]  # 由main_engine add_gateway调用
    get_file_path = GetFilePath()
    # ----------------------------------------------------------------------------------------------------
    def __init__(self, event_engine):
        """ """
        super().__init__(event_engine, "BYBITONE")
        self.orders: Dict[str, OrderData] = {}
        self.ws_spot_data_api = BybitWebsocketDataApi(self)
        self.ws_usdt_data_api = BybitWebsocketDataApi(self)
        self.ws_inverse_data_api = BybitWebsocketDataApi(self)
        self.ws_option_data_api = BybitWebsocketDataApi(self)
        self.rest_api = BybitRestApi(self)
        self.ws_trade_api = BybitWebsocketTradeApi(self)

        self.count: int = 0
        self.query_count: int = 0
        # 所有合约列表
        self.recording_list = self.get_file_path.recording_list
        self.recording_list = [vt_symbol for vt_symbol in self.recording_list if is_target_contract(vt_symbol, self.gateway_name)]
        # 历史数据合约列表
        self.history_contracts = copy(self.recording_list)
        # rest查询合约列表
        self.query_contracts = [vt_symbol for vt_symbol in self.get_file_path.all_trading_vt_symbols if is_target_contract(vt_symbol, self.gateway_name)]
        if not self.query_contracts:
            self.query_contracts = copy(self.recording_list)
        # 下载历史数据状态
        self.history_status: bool = True
        # 订阅逐笔成交数据状态
        self.book_trade_status: bool = False
        self.websocket_apis = [self.ws_spot_data_api, self.ws_usdt_data_api, self.ws_inverse_data_api, self.ws_option_data_api, self.ws_trade_api]
    # ----------------------------------------------------------------------------------------------------
    def connect(self, log_account: dict = {}):
        """ """
        if not log_account:
            log_account = bybitone_account
        key = log_account["key"]
        secret = log_account["secret"]
        server = log_account["server"]
        proxy_host = log_account["host"]
        proxy_port = log_account["port"]
        self.account_file_name = log_account["account_file_name"]
        self.rest_api.connect(key, secret, server, proxy_host, proxy_port)
        if server == "REAL":
            self.ws_spot_data_api.connect(SPOT_PUBLIC_WS_HOST, proxy_host, proxy_port)
            self.ws_usdt_data_api.connect(USDT_PUBLIC_WS_HOST, proxy_host, proxy_port)
            self.ws_inverse_data_api.connect(INVERSE_PUBLIC_WS_HOST, proxy_host, proxy_port)
            self.ws_option_data_api.connect(OPTION_PUBLIC_WS_HOST, proxy_host, proxy_port)
        else:
            self.ws_spot_data_api.connect(TESTNET_SPOT_PUBLIC_WS_HOST, proxy_host, proxy_port)
            self.ws_usdt_data_api.connect(TESTNET_USDT_PUBLIC_WS_HOST, proxy_host, proxy_port)
            self.ws_inverse_data_api.connect(TESTNET_INVERSE_PUBLIC_WS_HOST, proxy_host, proxy_port)
            self.ws_option_data_api.connect(TESTNET_OPTION_PUBLIC_WS_HOST, proxy_host, proxy_port)

        self.ws_trade_api.connect(key, secret, server, proxy_host, proxy_port)
        self.event_engine.register(EVENT_TIMER, self.process_timer_event)
        self.event_engine.register(EVENT_TIMER, self.process_query_functions)
        if self.history_status:
            self.event_engine.register(EVENT_TIMER, self.query_history)
    # ----------------------------------------------------------------------------------------------------
    def subscribe(self, req: SubscribeRequest):
        """ """
        exchange = req.exchange
        if exchange == Exchange.BYBITSPOT:
            self.ws_spot_data_api.subscribe(req)
        else:
            category = self.rest_api.get_category(req.vt_symbol)
            if category == "option":
                self.ws_option_data_api.subscribe(req)
            elif category == "linear":
                self.ws_usdt_data_api.subscribe(req)
            else:
                self.ws_inverse_data_api.subscribe(req)
    # ----------------------------------------------------------------------------------------------------
    def send_order(self, req: OrderRequest):
        """ """
        return self.rest_api.send_order(req)
    # ----------------------------------------------------------------------------------------------------
    def cancel_order(self, req: CancelRequest):
        """ """
        self.rest_api.cancel_order(req)
    # ----------------------------------------------------------------------------------------------------
    def query_account(self):
        """ """
        self.rest_api.query_account()
    # ----------------------------------------------------------------------------------------------------
    def query_order(self, vt_symbol: str):
        """
        查询活动委托单
        """
        self.rest_api.query_active_order(vt_symbol)
    # ----------------------------------------------------------------------------------------------------
    def query_position(self, vt_symbol: str):
        """
        查询持仓
        """
        self.rest_api.query_position(vt_symbol)
    # ----------------------------------------------------------------------------------------------------
    def process_query_functions(self,event):
        """
        轮询查询活动委托单和持仓
        """
        self.query_count += 1
        if self.query_count < 3:
            return
        self.query_count = 0
        if self.query_contracts:
            vt_symbol = self.query_contracts.pop(0)
            self.query_order(vt_symbol)
            self.query_position(vt_symbol)
            self.query_contracts.append(vt_symbol)
    # ----------------------------------------------------------------------------------------------------
    def process_timer_event(self, event):
        """
        处理定时任务
        """
        self.count += 1
        if self.count < 20:
            return
        self.count = 0
        self.query_account()

        for api in self.websocket_apis:
            api.send_packet({"op": "ping"})
    # ----------------------------------------------------------------------------------------------------
    def query_history(self, event):
        """
        查询合约历史数据
        """

        if self.history_contracts:
            vt_symbol = self.history_contracts.pop(0)
            symbol, exchange, gateway_name = extract_vt_symbol(vt_symbol)
            req = HistoryRequest(
                symbol=symbol,
                exchange=Exchange(exchange),
                interval=Interval.MINUTE,
                start=datetime.now(TZ_INFO) - timedelta(minutes=1440),
                end=datetime.now(TZ_INFO),
                gateway_name=self.gateway_name,
            )
            self.rest_api.query_history(req)
            self.rest_api.set_leverage(vt_symbol)
            self.rest_api.switch_isolated(vt_symbol)
            self.rest_api.switch_mode(vt_symbol)
    # -------------------------------------------------------------------------------------------------------
    def on_order(self, order: OrderData) -> None:
        """
        收到委托单推送，BaseGateway推送数据
        """
        self.orders[order.vt_orderid] = copy(order)
        super().on_order(order)
    # -------------------------------------------------------------------------------------------------------
    def get_order(self, vt_orderid: str) -> OrderData:
        """
        用vt_orderid获取委托单数据
        """
        return self.orders.get(vt_orderid, None)
    # ----------------------------------------------------------------------------------------------------
    def close(self):
        """ """
        self.rest_api.stop()
        for api in self.websocket_apis:
            api.stop()
# ----------------------------------------------------------------------------------------------------
class BybitRestApi(RestClient):
    """
    ByBit REST API
    """
    # ----------------------------------------------------------------------------------------------------
    def __init__(self, gateway: BybitOneGateway):
        """ """
        super().__init__()
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        self.key = ""
        self.secret = b""
        self.account_date = None  # 账户日期
        self.accounts_info: Dict[str, dict] = {}
        # 确保生成的orderid不发生冲突
        self.order_count: int = 0
        self.order_count_lock: Lock = Lock()
        self.count_datetime: int = 0
        self.time_offset:int = 0        # 本地与服务器的毫秒时间差整数值
    # ----------------------------------------------------------------------------------------------------
    def get_server_time(self):
        """
        获取服务器时间
        """
        self.add_request(
            "GET",
            "/v5/market/time",
            callback=self.on_server_time,
        )
    # ----------------------------------------------------------------------------------------------------
    def on_server_time(self, data: dict, request: Request):
        """
        收到服务器时间回报
        """
        server_time = get_local_datetime(int(data["result"]["timeNano"]))
        local_time = datetime.now(TZ_INFO)
        self.time_offset = int((local_time - server_time).total_seconds() * 1000)
        self.gateway.write_log(f"服务器时间：{server_time}，本地时间：{local_time}")
    # ----------------------------------------------------------------------------------------------------
    def sign(self, request: Request):
        """
        Generate ByBit signature.
        """
        if request.method == "GET":
            api_params = urlencode(request.params) if request.params else ""
        else:
            api_params = json.dumps(request.data if request.data else {})
            request.data = api_params

        recv_window = str(30 * 1000)
        nonce = str(int(time() * 1000) - self.time_offset)
        param_str = nonce + self.key + recv_window + api_params
        signature = hmac.new(self.secret, param_str.encode("utf-8"), hashlib.sha256).hexdigest()
        if not request.headers:
            request.headers = {"Content-Type": "application/json"}

        request.headers.update({"X-BAPI-API-KEY": self.key, "X-BAPI-SIGN": signature, "X-BAPI-TIMESTAMP": nonce, "X-BAPI-RECV-WINDOW": recv_window})
        return request
    # ----------------------------------------------------------------------------------------------------
    def connect(
        self,
        key: str,
        secret: str,
        server: str,
        proxy_host: str,
        proxy_port: int,
    ):
        """
        Initialize connection to REST server.
        """
        self.key = key
        self.secret = secret.encode()
        if server == "REAL":
            self.init(REST_HOST, proxy_host, proxy_port, gateway_name=self.gateway_name)
        else:
            self.init(TESTNET_REST_HOST, proxy_host, proxy_port, gateway_name=self.gateway_name)

        self.start()
        self.gateway.write_log(f"交易接口:{self.gateway_name},REST API启动成功")
        self.get_server_time()
        self.query_contract()
    # ----------------------------------------------------------------------------------------------------
    def get_category(self, vt_symbol: str):
        """
        通过vt_symbol获取产品类型
        """
        symbol, exchange, gateway_name = extract_vt_symbol(vt_symbol)
        if exchange == Exchange.BYBITSPOT:
            return "spot"
        # SOLUSDT-11APR25 U本位交割合约，BTCUSDZ25 币本位交割合约
        if symbol.endswith(("USDT", "PERP")) or ("-" in symbol and symbol[-2:].isdigit()):
            return "linear"
        elif symbol.endswith(("-C", "-P")):
            return "option"
        else:
            return "inverse"
    # ----------------------------------------------------------------------------------------------------
    def set_leverage(self, vt_symbol: str):
        """
        设置合约杠杆
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        category = self.get_category(vt_symbol)
        # 现货无法设置杠杆
        if category == "spot":
            return
        path = "/v5/position/set-leverage"
        data = {"category": category, "symbol": symbol, "buyLeverage": "10", "sellLeverage": "10"}
        self.add_request("POST", path, self.on_leverage, data=data, extra={"vt_symbol": vt_symbol})
    # ----------------------------------------------------------------------------------------------------
    def on_leverage(self, data: dict, request: Request):
        """
        * 收到设置杠杆回调
        * reMsg:110043杠杆没有修改,0杠杆修改成功
        """
        pass
    # ----------------------------------------------------------------------------------------------------
    def switch_isolated(self, vt_symbol: str):
        """
        设置全仓保证金模式，并设置标的杠杆
        不支持统一账户设置
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        category = self.get_category(vt_symbol)
        # 只支持统一账户U本位合约
        if category not in ["linear"]:
            return
        path = "/v5/position/switch-isolated"
        data = {"category": category, "symbol": symbol, "tradeMode": 0, "buyLeverage": "10", "sellLeverage": "10"}
        self.add_request("POST", path, self.on_isolated, data=data, extra={"vt_symbol": vt_symbol})
    # ----------------------------------------------------------------------------------------------------
    def on_isolated(self, data: dict, request: Request):
        """
        收到保证金模式回调
        """
        pass
    # ----------------------------------------------------------------------------------------------------
    def switch_mode(self, vt_symbol: str):
        """
        设置单向持仓模式
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        category = self.get_category(vt_symbol)
        # 只支持正向永续和反向永续设置持仓模式
        if category not in ["linear", "inverse"]:
            return
        path = "/v5/position/switch-mode"
        data = {"category": category, "symbol": symbol, "mode": 0}
        self.add_request("POST", path, self.on_mode, data=data, extra={"vt_symbol": vt_symbol})
    # ----------------------------------------------------------------------------------------------------
    def on_mode(self, data: dict, request: Request):
        """
        收到持仓模式回调
        """
        pass
    # ----------------------------------------------------------------------------------------------------
    def _new_order_id(self) -> int:
        """
        生成本地委托号
        """
        with self.order_count_lock:
            self.order_count += 1
            return self.order_count
    # ----------------------------------------------------------------------------------------------------
    def send_order(self, req: OrderRequest):
        """
        发送委托单
        """
        self.count_datetime = int(datetime.now().strftime("%Y%m%d%H%M%S"))

        category = self.get_category(req.vt_symbol)
        orderid = req.symbol + "-" + str(self.count_datetime) + str(self._new_order_id()).rjust(8,"0")
        data = {
            "category": category,
            "symbol": req.symbol,
            "price": str(req.price),
            "qty": str(req.volume),
            "side": DIRECTION_VT2BYBIT[req.direction],
            "orderType": ORDER_TYPE_VT2BYBIT[req.type],
            "orderLinkId": orderid,
            "positionIdx": "0",     # 单向持仓
            "timeInForce": TIMEINFORCE_MAP[req.type]      # 订单执行策略
        }
        # 平仓信号仅减仓，reduceOnly参数不适用于现货
        if req.offset == Offset.CLOSE and category != "spot":
            data["reduceOnly"] = True
        order = req.create_order_data(orderid, self.gateway_name)
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
        self.gateway.on_order(order)
        return order.vt_orderid
    # ----------------------------------------------------------------------------------------------------
    def on_send_order_failed(self, status_code, request: Request):
        """
        Callback when sending order failed on server.
        """
        order = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)
        data = request.response.json()
        if not data:
            return
        error_msg = data["retMsg"]
        error_code = data["retCode"]
        msg = f"发送委托失败，错误代码:{error_code},  错误信息：{error_msg}，委托单数据：{order}"
        self.gateway.write_log(msg)
    # ----------------------------------------------------------------------------------------------------
    def on_send_order_error(self, exception_type: type, exception_value: Exception, tracebacks, request: Request):
        """
        订单发送异常处理回调函数
        """
        order: OrderData = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)

        # Record exception if not ConnectionError
        if not issubclass(exception_type, ConnectionError):
            self.on_error(exception_type, exception_value, tracebacks, request)
    # ----------------------------------------------------------------------------------------------------
    def on_send_order(self, data: dict, request: Request):
        """ """
        if self.check_error("发送委托", data):
            order: OrderData = request.extra
            order.status = Status.REJECTED
            self.gateway.on_order(order)
            self.gateway.write_log(f"错误委托单：{order}")
            return
    # ----------------------------------------------------------------------------------------------------
    def cancel_order(self, req: CancelRequest):
        """ """
        order: OrderData = self.gateway.get_order(req.vt_orderid)
        data = {
            "category": self.get_category(req.vt_symbol),
            "orderLinkId": req.orderid,
            "symbol": req.symbol,
        }
        self.add_request("POST", path="/v5/order/cancel", data=data, callback=self.on_cancel_order, on_failed=self.on_cancel_failed, extra=order)
    # ----------------------------------------------------------------------------------------------------
    def on_cancel_order(self, data: dict, request: Request):
        """ """
        if self.check_error("取消委托", data):
            error_code = data["retCode"]
            # 重复撤销委托单被拒推送
            if error_code == 110001:
                order: OrderData = request.extra
                order.status = Status.REJECTED
                self.gateway.on_order(order)
            return
    # -------------------------------------------------------------------------------------------------------
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
    # ----------------------------------------------------------------------------------------------------
    def query_contract(self):
        """ """
        # params = ["linear", "inverse", "spot","option"]
        params = ["linear", "inverse", "spot"]
        for param in params:
            self.add_request("GET", "/v5/market/instruments-info", self.on_query_contract, params={"limit": 500, "status": "Trading", "category": param})
    # ----------------------------------------------------------------------------------------------------
    def check_error(self, name: str, data: dict):
        """ """
        if data["retCode"]:
            error_code = data["retCode"]
            error_msg = data["retMsg"]
            msg = f"{name}失败，错误代码：{error_code}，信息：{error_msg}"
            self.gateway.write_log(msg)
            return True

        return False
    # ----------------------------------------------------------------------------------------------------
    def on_query_contract(self, data: dict, request: Request):
        """
        查询合约
        """
        if self.check_error("查询合约", data):
            return
        raw = data["result"]
        category = raw["category"]
        product = CATEGORY_PRODUCT_MAP[category]

        for contract_data in raw["list"]:
            contract = ContractData(
                symbol=contract_data["symbol"],
                exchange=CATEGORY_EXCHANGE_MAP[category],
                name=contract_data["symbol"],
                product=product,
                size=10,  # 合约杠杆
                price_tick=float(contract_data["priceFilter"].get("minPrice", contract_data["priceFilter"]["tickSize"])),
                max_volume=float(contract_data["lotSizeFilter"]["maxOrderQty"]),
                min_volume=float(contract_data["lotSizeFilter"]["minOrderQty"]),
                gateway_name=self.gateway_name,
            )
            delivery_time = int(contract_data.get("deliveryTime", "0"))  # 交割时间
            if delivery_time:
                delivery_datetime = get_local_datetime(delivery_time)
                # 过滤过期合约
                if delivery_datetime <= datetime.now(TZ_INFO):
                    continue
                # 交割合约使用symbol_mark + 交割日期作为name
                contract.name = get_symbol_mark(contract.vt_symbol) + "_" + str(delivery_datetime.date())
            self.gateway.on_contract(contract)
        self.gateway.write_log(f"{self.gateway_name}，{category.upper()}合约信息查询成功")
        # 翻页游标
        next_cursor = raw.get("nextPageCursor")
        if next_cursor:
            self.add_request("GET", "/v5/market/instruments-info", self.on_query_contract, params={"limit": 500, "status": "Trading", "category": category,"cursor":next_cursor})
    # ----------------------------------------------------------------------------------------------------
    def get_float_value(self, value: str) -> float:
        """
        将字符串转换为浮点数，处理空值
        """
        return float(value) if value else 0
    # ----------------------------------------------------------------------------------------------------
    def query_account(self):
        """
        发送查询资金请求
        """
        self.add_request(method="GET", path="/v5/account/wallet-balance", callback=self.on_query_account, params={"accountType": "UNIFIED"})
    # ----------------------------------------------------------------------------------------------------
    def on_query_account(self, data: dict, request: Request):
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
                accountid=f"{coin}_{self.gateway_name}",
                balance=self.get_float_value(account_data["walletBalance"]),
                margin=self.get_float_value(account_data["totalPositionIM"]),
                position_profit=self.get_float_value(account_data["unrealisedPnl"]),
                close_profit=self.get_float_value(account_data["cumRealisedPnl"]),
                datetime=datetime.now(TZ_INFO),
                file_name=self.gateway.account_file_name,
                gateway_name=self.gateway_name,
            )
            total_order_margin = self.get_float_value(account_data["totalOrderIM"])     # 委托单占用保证金.
            locked = self.get_float_value(account_data["locked"])     # 现货挂单冻结金额
            account.available = account.balance - account.margin - total_order_margin - locked
            if account.balance:
                self.gateway.on_account(account)
                # 保存账户资金信息
                self.accounts_info[account.accountid] = account.__dict__
        if not self.accounts_info:
            return
        accounts_info = list(self.accounts_info.values())
        account_date = accounts_info[-1]["datetime"].date()
        account_path = self.gateway.get_file_path.account_path(self.gateway.account_file_name)
        write_header = not Path(account_path).exists()
        additional_writing = self.account_date and self.account_date != account_date
        self.account_date = account_date
        # 文件不存在则写入文件头，否则只在日期变更后追加写入文件
        if not write_header and not additional_writing:
            return
        write_mode = "w" if write_header else "a"
        for account_data in accounts_info:
            with open(account_path, write_mode, newline="") as f1:
                w1 = csv.DictWriter(f1, list(account_data))
                if write_header:
                    w1.writeheader()
                w1.writerow(account_data)
    # ----------------------------------------------------------------------------------------------------
    def query_position(self, vt_symbol: str):
        """
        发送查询持仓请求
        """
        symbol, exchange, gateway_name = extract_vt_symbol(vt_symbol)
        # 查询持仓不支持现货
        if exchange == Exchange.BYBITSPOT:
            return
        params = {"category": self.get_category(vt_symbol), "limit": 50, "symbol": symbol}
        path = "/v5/position/list"
        self.add_request(method="GET", path=path, callback=self.on_query_position, params=params)
    # ----------------------------------------------------------------------------------------------------
    def on_query_position(self, data: dict, request: Request):
        """
        收到持仓回报
        """
        if self.check_error("查询持仓", data):
            if data["retCode"] == 10002:
                self.gateway.write_log(f"交易接口：{self.gateway_name}，服务器时间与本地时间不同步，重启交易子进程")
                save_connection_status(self.gateway_name, False)
            return
        category = data["result"]["category"]
        exchange = CATEGORY_EXCHANGE_MAP[category]
        raw_data = data["result"]["list"]
        for pos_data in raw_data:
            direction = DIRECTION_BYBIT2VT.get(pos_data["side"], None)
            if direction:
                pos = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=direction,
                    volume=abs(float(pos_data["size"])),
                    price=float(pos_data["avgPrice"]),
                    pnl=float(pos_data["unrealisedPnl"]),  # 持仓盈亏
                    gateway_name=self.gateway_name,
                )
                self.gateway.on_position(pos)
            else:
                long_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.LONG,
                    volume=0,
                    price=0,
                    pnl=0,
                    frozen=0,
                    gateway_name=self.gateway_name,
                )
                short_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.SHORT,
                    volume=0,
                    price=0,
                    pnl=0,
                    frozen=0,
                    gateway_name=self.gateway_name,
                )
                self.gateway.on_position(long_position)
                self.gateway.on_position(short_position)
    # ----------------------------------------------------------------------------------------------------
    def query_active_order(self, vt_symbol: str):
        """
        发送查询活动委托单请求
        """
        symbol = extract_vt_symbol(vt_symbol)[0]
        params = {
            "category": self.get_category(vt_symbol),
            "limit": 20,
            "symbol": symbol,
        }
        path = "/v5/order/realtime"
        self.add_request("GET", path, callback=self.on_query_order, params=params)
    # ----------------------------------------------------------------------------------------------------
    def on_query_order(self, data: dict, request: Request):
        """
        收到活动委托单回报
        """
        if self.check_error("查询未成交委托", data):
            if data["retCode"] == "10001":
                delete_dr_data(request.params["symbol"], self.gateway_name)
            return
        result = data["result"]["list"]
        if not result:
            return
        category = data["result"]["category"]
        exchange = CATEGORY_EXCHANGE_MAP[category]
        for order_data in result:
            order = OrderData(
                symbol=order_data["symbol"],
                exchange=exchange,
                orderid=order_data["orderLinkId"],
                type=ORDER_TYPE_BYBIT2VT[order_data["timeInForce"]],
                direction=DIRECTION_BYBIT2VT[order_data["side"]],
                price=float(order_data["price"]),
                volume=float(order_data["qty"]),
                traded=float(order_data["cumExecQty"]),
                status=STATUS_BYBIT2VT[order_data["orderStatus"]],
                datetime=get_local_datetime(int(order_data["createdTime"])),
                gateway_name=self.gateway_name,
            )
            if order_data["reduceOnly"]:
                order.offset = Offset.CLOSE
            self.gateway.on_order(order)
    # ----------------------------------------------------------------------------------------------------
    def query_history(self, req: HistoryRequest) -> List[BarData]:
        """
        查询历史数据
        """
        history = []
        count = 200  # 交易所限制获取分钟bar数量
        start_time = req.start
        time_consuming_start = time()

        while start_time < req.end:
            end_time = start_time + timedelta(minutes=count)
            params = {
                "category": self.get_category(req.vt_symbol),
                "symbol": req.symbol,
                "interval": INTERVAL_VT2BYBIT[req.interval],
                "start": int(start_time.timestamp() * 1000),
                "end": int(end_time.timestamp() * 1000),
                "limit": count,
            }
            
            resp = self.request("GET", "/v5/market/kline", params=params)
            if not resp or resp.status_code // 100 != 2:
                msg = f"合约：{req.vt_symbol}，获取历史数据失败，状态码：{resp.status_code if resp else '无响应'}"
                self.gateway.write_log(msg)
                break
            
            data = resp.json()
            if not data or data["retCode"] == 10001 or not data["result"]:
                msg = f"无法获取合约：{req.vt_symbol}历史数据"
                self.gateway.write_log(msg)
                delete_dr_data(req.symbol, self.gateway_name)
                break

            buf = [BarData(
                symbol=req.symbol,
                exchange=req.exchange,
                datetime=get_local_datetime(int(d[0])),
                interval=req.interval,
                open_price=float(d[1]),
                high_price=float(d[2]),
                low_price=float(d[3]),
                close_price=float(d[4]),
                volume=float(d[6] if req.symbol.endswith("USD") else d[5]),     # 反向合约币的成交量是成交额，其他合约币的成交量即为币的成交量
                gateway_name=self.gateway_name,
            ) for d in data["result"]["list"]]
            
            if not buf:
                break
            history.extend(buf)
            start_time += timedelta(minutes=count)
            if len(buf) < count:
                break

        history.sort(key=lambda x: x.datetime)
        if history:
            try:
                database_manager.save_bar_data(history, False)
            except Exception as err:
                self.gateway.write_log(str(err))
                return

            time_consuming_end = time()
            query_time = round(time_consuming_end - time_consuming_start, 3)
            msg = f"载入{req.vt_symbol} bar数据，开始时间：{history[0].datetime}，结束时间：{history[-1].datetime}，数据量：{len(history)}，耗时：{query_time}秒"
            self.gateway.write_log(msg)
        else:
            msg = f"未查询到合约：{req.vt_symbol}历史数据，请核实行情连接"
            self.gateway.write_log(msg)
# ----------------------------------------------------------------------------------------------------
class BybitWebsocketDataApi(WebsocketClient):
    """ """

    def __init__(self, gateway: BybitOneGateway):
        """ """
        super().__init__()

        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        # 产品类型
        self.category: str = ""

        self.callbacks: Dict[str, Callable] = {}
        self.ticks: Dict[str, TickData] = {}
        self.subscribed: Dict[str, SubscribeRequest] = {}

        self.order_book_bids = defaultdict(dict)  # 订单簿买单字典
        self.order_book_asks = defaultdict(dict)  # 订单簿卖单字典
    # ----------------------------------------------------------------------------------------------------
    def connect(self, url: str, proxy_host: str, proxy_port: int):
        """ """
        self.proxy_host = proxy_host
        self.proxy_port = proxy_port
        self.category = url.split("/")[-1].upper()

        self.init(url, self.proxy_host, self.proxy_port, gateway_name=self.gateway_name)
        self.start()
    # ----------------------------------------------------------------------------------------------------
    def subscribe(self, req: SubscribeRequest):
        """
        订阅tick行情
        """
        self.subscribed[req.vt_symbol] = req

        tick = TickData(symbol=req.symbol, exchange=req.exchange, datetime=datetime.now(TZ_INFO), name=req.symbol, gateway_name=self.gateway_name)
        self.ticks[req.symbol] = tick
        # 订阅100ms tick行情
        self.subscribe_topic(f"tickers.{req.symbol}", self.on_tick)
            
        # 触发订阅逐笔成交状态则订阅成交数据和20ms深度行情否则订阅100ms深度行情
        category = self.gateway.rest_api.get_category(tick.vt_symbol)
        is_option = category == "option"
        
        if self.gateway.book_trade_status:
            self.subscribe_topic(f"publicTrade.{req.symbol}", self.on_public_trade)
            # 推送频率20ms对应订阅档位
            depth_level = 25 if is_option else 50
        else:
            # 推送频率100ms对应订阅档位，合约200档推送频率100ms，现货200档推送频率200ms
            depth_level = 100 if is_option else 200
        self.subscribe_topic(f"orderbook.{depth_level}.{req.symbol}", self.on_depth)
    # ----------------------------------------------------------------------------------------------------
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
    # ----------------------------------------------------------------------------------------------------
    def on_connected(self):
        """ """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API {self.category}行情连接成功")
        for req in list(self.subscribed.values()):
            self.subscribe(req)
    # ----------------------------------------------------------------------------------------------------
    def on_disconnected(self):
        """ """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API {self.category}行情连接断开")
    # ----------------------------------------------------------------------------------------------------
    def on_packet(self, packet: dict):
        """ """
        # 过滤心跳回报
        if packet.get("op", None) in ["ping", "pong"]:
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
                # 删除已过期合约
                if "error:handler not found" in ret_msg:
                    symbol = ret_msg.split(".")[1]
                    delete_dr_data(symbol, self.gateway_name)
                self.gateway.write_log(f"交易接口：{self.gateway_name}，Websocket API出错，错误信息：{ret_msg}")
    # ----------------------------------------------------------------------------------------------------
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
        # 收到快照数据推送(订阅tick数据后只推送一次)
        if type_ == "snapshot":
            tick.high_price = float(data["highPrice24h"])
            tick.low_price = float(data["lowPrice24h"])
            tick.pre_close = float(data["prevPrice24h"])

        if "openInterest" in data:
            tick.open_interest = float(data["openInterest"])
        if "lastPrice" in data:
            tick.last_price = float(data["lastPrice"])
        if "volume24h" in data:
            tick.volume = float(data["volume24h"])      # 最近24小时币的成交量
        # snapshot和delta都推送的数据
        if "bid1Price" in data:
            tick.bid_price_1 = float(data["bid1Price"])
            tick.bid_volume_1 = float(data["bid1Size"])
        if "ask1Price" in data:
            tick.ask_price_1 = float(data["ask1Price"])
            tick.ask_volume_1 = float(data["ask1Size"])

        tick.datetime = get_local_datetime(int(timestamp))
    # ----------------------------------------------------------------------------------------------------
    def on_depth(self, packet: dict):
        """ """
        data = packet["data"]
        symbol = data["s"]
        tick = self.ticks[symbol]
        tick.datetime = get_local_datetime(int(packet["ts"]))

        # 判断是否为全量数据推送，是则清空order book
        if packet["type"] == "snapshot":
            self.order_book_bids[symbol].clear()
            self.order_book_asks[symbol].clear()

        # 辅助函数：更新order book
        def update_order_book(order_book, data):
            for price, amount in data:
                if float(amount) == 0:
                    order_book.pop(price, None)  # 委托量为0则删除
                else:
                    order_book[price] = amount  # 更新或添加

        update_order_book(self.order_book_bids[symbol], data["b"])
        update_order_book(self.order_book_asks[symbol], data["a"])

        # 辅助函数：设置tick的价格和量
        def set_tick_attributes(tick, sorted_data, prefix):
            for index, (price, volume) in enumerate(sorted_data, start=1):
                setattr(tick, f"{prefix}_price_{index}", float(price))
                setattr(tick, f"{prefix}_volume_{index}", float(volume))

        # 排序并更新tick
        # 买单价格从高到低排序
        sort_bids = sorted(self.order_book_bids[symbol].items(), key=lambda x: float(x[0]), reverse=True)[:5]
        # 卖单价格从低到高排序
        sort_asks = sorted(self.order_book_asks[symbol].items(), key=lambda x: float(x[0]))[:5]
        set_tick_attributes(tick, sort_bids, "bid")
        set_tick_attributes(tick, sort_asks, "ask")
        # 如果有最新价格，触发tick更新
        if tick.last_price:
            self.gateway.on_tick(copy(tick))
    # ----------------------------------------------------------------------------------------------------
    def on_public_trade(self, packet: dict):
        """
        收到逐笔成交回报
        """
        data = packet["data"]
        for trade_data in data:
            symbol = trade_data["s"]
            tick = self.ticks[symbol]
            tick.last_price = float(trade_data["p"])
            tick.datetime = get_local_datetime(trade_data["T"])
            self.gateway.on_tick(copy(tick))
# ----------------------------------------------------------------------------------------------------
class BybitWebsocketTradeApi(WebsocketClient):
    def __init__(self, gateway: BybitOneGateway):
        """ """
        super().__init__()
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name

        self.key = ""
        self.secret = b""
        self.callbacks: Dict[str, Callable] = {}
    # ----------------------------------------------------------------------------------------------------
    def connect(
        self,
        key: str,
        secret: str,
        server: str,
        proxy_host: str,
        proxy_port: int,
    ):
        """ """
        self.key = key
        self.secret = secret.encode()
        self.proxy_host = proxy_host
        self.proxy_port = proxy_port
        self.server = server

        if self.server == "REAL":
            url = PRIVATE_WS_HOST
        else:
            url = TESTNET_PRIVATE_WS_HOST

        self.init(url, self.proxy_host, self.proxy_port, gateway_name=self.gateway_name)
        self.start()
    # ----------------------------------------------------------------------------------------------------
    def login(self):
        """
        """
        expires = int((time() + 30) * 1000)
        msg = f"GET/realtime{expires}"
        signature = hmac.new(self.secret, msg.encode(), hashlib.sha256).hexdigest()

        req = {"op": "auth", "args": [self.key, expires, signature]}
        self.send_packet(req)
    # ----------------------------------------------------------------------------------------------------
    def on_login(self):
        """
        收到登录回报
        """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API登录成功")
        self.subscribe_topic("order", self.on_order)
        #self.subscribe_topic("execution", self.on_trade)       # 全品种成交推送
        self.subscribe_topic("execution.fast", self.on_trade)       # 不支持期权
        self.subscribe_topic("position", self.on_position)
    # ----------------------------------------------------------------------------------------------------
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
    # ----------------------------------------------------------------------------------------------------
    def on_packet(self, packet: dict):
        """ """
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
    # ----------------------------------------------------------------------------------------------------
    def on_connected(self):
        """ """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API交易连接成功")
        self.login()
    # ----------------------------------------------------------------------------------------------------
    def on_disconnected(self):
        """ """
        self.gateway.write_log(f"交易接口:{self.gateway_name},Websocket API交易连接断开")
    # ----------------------------------------------------------------------------------------------------
    def on_trade(self, packet):
        """
        收到成交回报
        """
        for trade_data in packet["data"]:
            category = trade_data["category"]
            exchange = CATEGORY_EXCHANGE_MAP[category]
            orderId = trade_data.get("orderLinkId", None)
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
                datetime=trade_datetime,
                gateway_name=self.gateway_name,
            )
            self.gateway.on_trade(trade)
    # ----------------------------------------------------------------------------------------------------
    def on_order(self, packet):
        """
        收到委托单回报
        """
        for order_data in packet["data"]:
            category = order_data["category"]
            exchange = CATEGORY_EXCHANGE_MAP[category]
            order = OrderData(
                symbol=order_data["symbol"],
                exchange=exchange,
                orderid=order_data["orderLinkId"],
                type=ORDER_TYPE_BYBIT2VT[order_data["timeInForce"]],
                direction=DIRECTION_BYBIT2VT[order_data["side"]],
                price=float(order_data["price"]),
                volume=float(order_data["qty"]),
                traded=float(order_data["cumExecQty"]),
                status=STATUS_BYBIT2VT[order_data["orderStatus"]],
                datetime=get_local_datetime(int(order_data["createdTime"])),
                gateway_name=self.gateway_name,
            )
            if order_data["reduceOnly"]:
                order.offset = Offset.CLOSE
            self.gateway.on_order(order)
    # ----------------------------------------------------------------------------------------------------
    def on_position(self, packet):
        """
        收到持仓回报
        """
        for pos_data in packet["data"]:
            # 通过杠杆区分现货，合约
            if pos_data["leverage"] == "10":
                exchange = Exchange.BYBIT
            else:
                exchange = Exchange.BYBITSPOT
            direction = DIRECTION_BYBIT2VT.get(pos_data["side"], None)
            if direction:
                pos = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=direction,
                    volume=abs(float(pos_data["size"])),
                    price=float(pos_data["entryPrice"]),
                    pnl=float(pos_data["unrealisedPnl"]),
                    gateway_name=self.gateway_name,
                )
                self.gateway.on_position(pos)
            else:
                long_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.LONG,
                    volume=0,
                    price=0,
                    pnl=0,
                    frozen=0,
                    gateway_name=self.gateway_name,
                )
                short_position = PositionData(
                    symbol=pos_data["symbol"],
                    exchange=exchange,
                    direction=Direction.SHORT,
                    volume=0,
                    price=0,
                    pnl=0,
                    frozen=0,
                    gateway_name=self.gateway_name,
                )
                self.gateway.on_position(long_position)
                self.gateway.on_position(short_position)
