import ccxt
import pyodbc
import time
import threading
from datetime import datetime, timedelta
from decimal import Decimal
import os
from dotenv import load_dotenv
import logging
from rich.console import Console
from rich.table import Table
from rich.layout import Layout
from rich.live import Live
from rich.panel import Panel
from rich.text import Text

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('trading_bot.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class TerminalDashboard:
    def __init__(self):
        self.console = Console()
        self.layout = Layout()
        self.last_update = datetime.now()
        
        # Split the layout
        self.layout.split(
            Layout(name="header", size=3),
            Layout(name="main", ratio=1),
            Layout(name="footer", size=3)
        )
        self.main = self.layout["main"]
        self.main.split_row(
            Layout(name="left"),
            Layout(name="right")
        )
        self.left = self.main["left"]
        self.right = self.main["right"]
        
    def update_dashboard(self, bot):
        """Update all dashboard panels"""
        self.last_update = datetime.now()
        
        # Header
        self.layout["header"].update(
            Panel(Text(f"Binance Futures Bot | Last Update: {self.last_update.strftime('%Y-%m-%d %H:%M:%S')}", 
                  justify="center", style="bold blue"))
        )
        
        # Balance Panel
        balance_text = Text()
        balance_text.append(f"Total Balance: {bot.total_balance:.2f} USDT\n", style="green")
        balance_text.append(f"Used Margin: {bot.used_margin:.2f} USDT\n", style="yellow")
        balance_text.append(f"Available: {(bot.total_balance - bot.used_margin):.2f} USDT", style="blue")
        
        # Positions Table
        positions_table = Table(title="Open Positions", show_lines=True)
        for col in ["Symbol", "Side", "Amount", "Entry", "Current", "PnL"]:
            positions_table.add_column(col)
        
        for symbol, pos in bot.positions.items():
            current_price = bot.mark_prices.get(symbol, Decimal('0'))
            pnl = bot.calculate_pnl(
                pos['side'], 
                pos['amount'], 
                pos['entryPrice'], 
                current_price, 
                pos['leverage']
            )
            positions_table.add_row(
                symbol.replace('/USDT', ''),
                pos['side'],
                f"{pos['amount']:.4f}",
                f"{pos['entryPrice']:.4f}",
                f"{current_price:.4f}",
                f"{pnl:.2f}%",
                style="green" if pnl >= 0 else "red"
            )
        
        # Prices Table (Top 10)
        prices_table = Table(title="Market Prices", show_lines=True)
        for col in ["Symbol", "Last", "Mark"]:
            prices_table.add_column(col)
        
        for symbol, price in list(bot.last_prices.items())[:10]:
            prices_table.add_row(
                symbol.replace('/USDT', ''),
                f"{price:.4f}",
                f"{bot.mark_prices.get(symbol, Decimal('0')):.4f}"
            )
        
        # Recent Trades (Last 10)
        trades_table = Table(title="Recent Trades", show_lines=True)
        for col in ["Time", "Symbol", "Side", "Qty", "Price", "Status"]:
            trades_table.add_column(col)
        
        for trade in bot.trade_history[-10:]:
            trades_table.add_row(
                trade['time'],
                trade['symbol'],
                trade['side'],
                f"{Decimal(trade['qty']):.4f}",
                f"{Decimal(trade['price']):.4f}" if trade['price'] != 'N/A' else 'N/A',
                trade['status'],
                style="green" if trade['status'] == 'EXECUTED' else "red"
            )
        
        # Update Layout
        self.left.update(
            Layout(
                Panel(balance_text, title="Balance"),
                Panel(positions_table)
            )
        )
        self.right.update(
            Layout(
                Panel(prices_table),
                Panel(trades_table)
            )
        )
        
        # Footer
        self.layout["footer"].update(
            Panel(Text("Press Ctrl+C to exit", justify="center", style="bold yellow"))
        )
        
        return self.layout

class BinanceFuturesBot:
    def __init__(self):
        load_dotenv()
        self.dashboard = TerminalDashboard()
        
        # Config
        self.BALANCE_PER_SYMBOL = Decimal(os.getenv('BALANCE_PER_SYMBOL', '1000'))
        self.SAFETY_MARGIN = Decimal(os.getenv('SAFETY_MARGIN', '0.9'))
        self.SLIPPAGE_TOLERANCE = Decimal(os.getenv('SLIPPAGE_TOLERANCE', '0.005'))
        self.MIN_REOPEN_DELAY = int(os.getenv('MIN_REOPEN_DELAY', '60'))
        
        # Init
        self.init_exchange()
        self.init_database()
        self.init_trading_data()
        
        # Threads
        self.running = True
        self.start_background_threads()

    def init_exchange(self):
        self.exchange = ccxt.binance({
            'apiKey': os.getenv('BINANCE_API_KEY'),
            'secret': os.getenv('BINANCE_API_SECRET'),
            'enableRateLimit': True,
            'options': {'defaultType': 'future'}
        })
        logger.info("Exchange connected")

    def init_database(self):
        try:
            conn_str = (
                f"DRIVER={os.getenv('SQL_DRIVER')};"
                f"SERVER={os.getenv('SQL_SERVER')};"
                f"DATABASE={os.getenv('SQL_DATABASE')};"
                f"UID={os.getenv('SQL_USERNAME')};"
                f"PWD={os.getenv('SQL_PASSWORD')};"
            )
            self.db_conn = pyodbc.connect(conn_str)
            self.db_cursor = self.db_conn.cursor()
            logger.info("Database connected")
        except Exception as e:
            logger.error(f"Database error: {e}")
            raise

    def init_trading_data(self):
        self.last_prices = {}
        self.mark_prices = {}
        self.last_closed_time = {}
        self.total_balance = Decimal('0')
        self.used_margin = Decimal('0')
        self.positions = {}
        self.trade_history = []
        self.status_mapping = {
            'PENDING': 0,
            'OPEN': 1,
            'CLOSED': 2,
            'CANCELED': 3,
            'FAILED': 4
        }

    def start(self):
        with Live(self.dashboard.layout, refresh_per_second=4, screen=True) as live:
            while self.running:
                try:
                    live.update(self.dashboard.update_dashboard(self))
                    time.sleep(1)
                except KeyboardInterrupt:
                    self.running = False
                except Exception as e:
                    logger.error(f"Dashboard error: {e}")
                    time.sleep(5)

    def start_background_threads(self):
        threads = [
            threading.Thread(target=self.monitor_prices_and_balance, daemon=True),
            threading.Thread(target=self.process_signals, daemon=True),
            threading.Thread(target=self.monitor_positions, daemon=True)
        ]
        for t in threads:
            t.start()
        logger.info("Background threads started")

    def monitor_prices_and_balance(self):
        while self.running:
            try:
                tickers = self.exchange.fetch_tickers()
                for symbol, ticker in tickers.items():
                    if symbol.endswith('/USDT'):
                        self.last_prices[symbol] = Decimal(str(ticker['last']))
                        self.mark_prices[symbol] = Decimal(str(ticker['info']['markPrice']))
                
                balance = self.exchange.fetch_balance()
                self.total_balance = Decimal(str(balance['USDT']['total']))
                self.used_margin = Decimal(str(balance['USDT']['used']))
                
                # Update positions from exchange
                self.positions = {}
                for pos in balance['info']['positions']:
                    if Decimal(pos['positionAmt']) != 0:
                        symbol = pos['symbol'].replace('USDT', '') + '/USDT'
                        self.positions[symbol] = {
                            'side': 'LONG' if Decimal(pos['positionAmt']) > 0 else 'SHORT',
                            'amount': abs(Decimal(pos['positionAmt'])),
                            'entryPrice': Decimal(pos['entryPrice']),
                            'leverage': int(pos['leverage'])
                        }
                
                time.sleep(5)
            except Exception as e:
                logger.error(f"Price monitoring error: {e}")
                time.sleep(10)

    def process_signals(self):
        while self.running:
            try:
                self.db_cursor.execute("EXEC sp_tranTF_last")
                signals = self.db_cursor.fetchall()
                
                if signals:
                    logger.info(f"Processing {len(signals)} signals")
                    
                    for signal in signals:
                        try:
                            signal_id = signal.id
                            symbol = signal.symbol
                            posisi = signal.posisi.upper()
                            price_open = Decimal(str(signal.price_open))
                            leverage = signal.leverage
                            stop_lose = Decimal(str(signal.stop_lose))
                            take_profit = Decimal(str(signal.take_profit))
                            signal_ch = signal.signal_score
                            
                            binance_symbol = f"{symbol}/USDT"
                            mark_price = self.mark_prices.get(binance_symbol, Decimal('0'))
                            
                            # Trigger condition
                            trigger_met = False
                            if posisi == "LONG" and mark_price <= price_open:
                                trigger_met = True
                            elif posisi == "SHORT" and mark_price >= price_open:
                                trigger_met = True
                            
                            if not trigger_met:
                                continue
                            
                            # Margin check
                            available = (self.total_balance - self.used_margin) * self.SAFETY_MARGIN
                            if available < self.BALANCE_PER_SYMBOL:
                                logger.warning(f"Insufficient margin for {symbol}")
                                continue
                            
                            # Slippage calculation
                            if posisi == "LONG":
                                worst_price = mark_price * (1 + self.SLIPPAGE_TOLERANCE)
                            else:
                                worst_price = mark_price * (1 - self.SLIPPAGE_TOLERANCE)
                            
                            qty = (self.BALANCE_PER_SYMBOL * leverage) / worst_price
                            qty = self.adjust_quantity_precision(symbol, qty)
                            
                            # Prevent rapid re-entry
                            last_closed = self.last_closed_time.get(binance_symbol)
                            if last_closed and (datetime.now() - last_closed).seconds < self.MIN_REOPEN_DELAY:
                                continue
                            
                            # Execute order
                            self.set_leverage(symbol, leverage)
                            order_result = self.execute_order(symbol, posisi, qty)
                            
                            if order_result:
                                exec_price = Decimal(str(order_result['price'])) if order_result['price'] else mark_price
                                self.update_signal_status(
                                    signal_id=signal_id,
                                    status='OPEN',
                                    binance_order_id=order_result['id'],
                                    price_open=exec_price,
                                    leverage=leverage,
                                    stop_lose=stop_lose,
                                    take_profit=take_profit,
                                    signal_ch=signal_ch
                                )
                            else:
                                self.update_signal_status(signal_id, 'FAILED')
                
                time.sleep(10)
            except Exception as e:
                logger.error(f"Signal processing error: {e}")
                time.sleep(30)

    def monitor_positions(self):
        while self.running:
            try:
                self.db_cursor.execute("""
                    SELECT id, symbol, binance_order_id, posisi, qty, price_open, 
                           stop_lose, take_profit, leverage, signal_score
                    FROM tran_TF 
                    WHERE status = 1""")
                open_positions = self.db_cursor.fetchall()
                
                if open_positions:
                    for position in open_positions:
                        try:
                            position_id = position.id
                            symbol = position.symbol
                            db_posisi = position.posisi.upper()
                            db_qty = Decimal(str(position.qty))
                            price_open = Decimal(str(position.price_open))
                            stop_lose = Decimal(str(position.stop_lose))
                            take_profit = Decimal(str(position.take_profit))
                            leverage = position.leverage
                            db_signal_ch = position.signal_score
                            
                            binance_symbol = f"{symbol}/USDT"
                            current_price = self.mark_prices.get(binance_symbol, Decimal('0'))
                            
                            # Check if should close
                            should_close = False
                            close_reason = ""
                            
                            # Position mismatch check
                            current_pos = self.positions.get(binance_symbol)
                            if not current_pos:
                                should_close = True
                                close_reason = "Position Not Found"
                            elif current_pos['side'] != db_posisi:
                                should_close = True
                                close_reason = "Position Mismatch"
                            
                            # TP/SL check
                            if not should_close:
                                if db_posisi == 'LONG':
                                    if current_price <= stop_lose:
                                        should_close = True
                                        close_reason = "Stop Loss"
                                    elif current_price >= take_profit:
                                        should_close = True
                                        close_reason = "Take Profit"
                                elif db_posisi == 'SHORT':
                                    if current_price >= stop_lose:
                                        should_close = True
                                        close_reason = "Stop Loss"
                                    elif current_price <= take_profit:
                                        should_close = True
                                        close_reason = "Take Profit"
                            
                            if should_close:
                                self.close_position(
                                    position_id=position_id,
                                    symbol=symbol,
                                    posisi=db_posisi,
                                    qty=db_qty,
                                    price_open=price_open,
                                    current_price=current_price,
                                    leverage=leverage,
                                    close_reason=close_reason
                                )
                        
                        except Exception as e:
                            logger.error(f"Position monitoring error: {e}")
                            continue
                
                time.sleep(15)
            except Exception as e:
                logger.error(f"Position monitor error: {e}")
                time.sleep(30)

    def execute_order(self, symbol, posisi, qty):
        try:
            binance_symbol = f"{symbol}/USDT"
            side = 'buy' if posisi == 'LONG' else 'sell'
            
            order = self.exchange.create_order(
                symbol=binance_symbol,
                type='MARKET',
                side=side,
                amount=float(qty),
                params={'positionSide': 'BOTH'}
            )
            
            order_details = self.exchange.fetch_order(order['id'], binance_symbol)
            
            # Record trade
            trade = {
                'time': datetime.now().strftime('%H:%M:%S'),
                'symbol': symbol,
                'side': posisi,
                'qty': str(qty),
                'price': order_details.get('price', 'N/A'),
                'status': 'EXECUTED',
                'type': 'OPEN'
            }
            self.trade_history.append(trade)
            
            return order_details
        except Exception as e:
            logger.error(f"Order execution error: {e}")
            
            # Record failed trade
            self.trade_history.append({
                'time': datetime.now().strftime('%H:%M:%S'),
                'symbol': symbol,
                'side': posisi,
                'qty': str(qty),
                'price': 'N/A',
                'status': f"FAILED: {str(e)}",
                'type': 'OPEN'
            })
            return None

    def close_position(self, position_id, symbol, posisi, qty, price_open, current_price, leverage, close_reason):
        try:
            binance_symbol = f"{symbol}/USDT"
            
            # Prevent rapid re-close
            if binance_symbol in self.last_closed_time:
                if (datetime.now() - self.last_closed_time[binance_symbol]).seconds < self.MIN_REOPEN_DELAY:
                    return False
            
            close_side = 'sell' if posisi == 'LONG' else 'buy'
            close_order = self.execute_order(symbol, close_side, qty)
            
            if close_order:
                pnl = self.calculate_pnl(posisi, qty, price_open, current_price, leverage)
                
                self.update_signal_status(
                    signal_id=position_id,
                    status='CLOSED',
                    binance_close_id=close_order['id'],
                    price_close=current_price,
                    pnl_real=pnl,
                    close_reason=close_reason
                )
                
                self.last_closed_time[binance_symbol] = datetime.now()
                return True
            return False
        except Exception as e:
            logger.error(f"Close position error: {e}")
            return False

    def calculate_pnl(self, posisi, qty, entry_price, exit_price, leverage):
        qty = Decimal(str(qty))
        entry = Decimal(str(entry_price))
        exit_px = Decimal(str(exit_price))
        lev = Decimal(str(leverage))
        
        if posisi == 'LONG':
            return ((exit_px - entry) / entry * lev * 100)
        else:
            return ((entry - exit_px) / entry * lev * 100)

    def set_leverage(self, symbol, leverage):
        try:
            self.exchange.set_leverage(leverage, f"{symbol}/USDT")
        except Exception as e:
            logger.error(f"Set leverage error: {e}")

    def adjust_quantity_precision(self, symbol, qty):
        market = self.exchange.market(f"{symbol}/USDT")
        return round(Decimal(qty), market['precision']['amount'])

    def update_signal_status(self, signal_id, status, **kwargs):
        try:
            status_code = self.status_mapping[status]
            
            if status == 'OPEN':
                self.db_cursor.execute("""
                    UPDATE tran_TF 
                    SET binance_order_id = ?, price_open = ?, leverage = ?, 
                        stop_lose = ?, take_profit = ?, status = ?, signal_score = ?, timestamp = GETDATE()
                    WHERE id = ?""",
                    kwargs.get('binance_order_id'), 
                    float(kwargs.get('price_open')), 
                    kwargs.get('leverage'),
                    float(kwargs.get('stop_lose')),
                    float(kwargs.get('take_profit')),
                    status_code,
                    kwargs.get('signal_ch'),
                    signal_id
                )
            elif status == 'CLOSED':
                self.db_cursor.execute("""
                    UPDATE tran_TF 
                    SET binance_close_id = ?, price_close = ?, status = ?, 
                        pnl_real = ?, close_reason = ?, timestamp = GETDATE()
                    WHERE id = ?""",
                    kwargs.get('binance_close_id'), 
                    float(kwargs.get('price_close')),
                    status_code,
                    float(kwargs.get('pnl_real')),
                    kwargs.get('close_reason', ''),
                    signal_id
                )
            else:
                self.db_cursor.execute("""
                    UPDATE tran_TF 
                    SET status = ?, timestamp = GETDATE()
                    WHERE id = ?""",
                    status_code,
                    signal_id
                )
            self.db_conn.commit()
        except Exception as e:
            logger.error(f"Update status error: {e}")

    def __del__(self):
        try:
            if hasattr(self, 'db_cursor'):
                self.db_cursor.close()
            if hasattr(self, 'db_conn'):
                self.db_conn.close()
        except Exception as e:
            logger.error(f"Cleanup error: {e}")

if __name__ == "__main__":
    try:
        bot = BinanceFuturesBot()
        bot.start()
    except Exception as e:
        logger.error(f"Fatal error: {e}")
