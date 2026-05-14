import MetaTrader5 as mt5
import pandas as pd
from datetime import datetime, timedelta
import time
import platform
import os
import json
import logging
import math
import random

# ----------------- CONFIG -----------------
# Changed currency pairs to Gold and Silver
SYMBOLS = ["XAUUSD", "XAGUSD"] 
TIMEFRAME_EXEC = mt5.TIMEFRAME_M1
TIMEFRAME_TREND = mt5.TIMEFRAME_M5
TIMEFRAME_M15 = mt5.TIMEFRAME_M15
TIMEFRAME_M30 = mt5.TIMEFRAME_M30

# --- CONFIG SECTION ---
SLEEP_INTERVAL = 2.0
M30_UPDATE_INTERVAL = 1.5

# Adjusted lots for Metals (0.01 is usually the minimum on Forex/Metals brokers)
MIN_LOT = 0.01
MAX_LOT = 10.0
MAGIC_BASE = 500000
POSITIONS_TO_OPEN = 3
MIN_HOLD_TIME = 60
COOLDOWN_SECONDS = 10
# Adjusted spread points for Metals (e.g., 500 points = 50 pips)
MAX_SPREAD_POINTS = 500 

RISK_PER_POSITION = 0.01
TP_MULTIPLIER = 1.5
TRAILING_STOP_POINTS = 500
DAILY_PROFIT_TARGET = 500.0
DAILY_LOSS_LIMIT = -10000.0

# --- GROWTH STRATEGY CONFIG ---
GROWTH_SYMBOL = "XAUUSD" # Updated to Gold
GROWTH_MIN_BAL = 50.0
GROWTH_MAX_BAL = 900.0
GROWTH_LOT = 0.1 # Adjusted for standard forex/metal accounts
GROWTH_HOLD_CANDLES = 3 
GROWTH_TF_EXIT = mt5.TIMEFRAME_M5

# Setup Logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger("Scalper")

symbol_cooldowns = {symbol: datetime.min for symbol in SYMBOLS}
m30_bias_cache = {symbol: "NEUTRAL" for symbol in SYMBOLS}

# ----------------- INITIALIZATION -----------------
def initialize_mt5():
    if not mt5.initialize():
        logger.error(f"MT5 initialize failed: {mt5.last_error()}")
        return False
    logger.info("MT5 initialized successfully")
    return True

# ----------------- UTILITIES (HARDENING) -----------------
def get_symbol_digits(symbol):
    info = mt5.symbol_info(symbol)
    return info.digits if info else 2

def get_filling_mode(symbol):
    """Corrected to avoid AttributeError on some MT5 versions"""
    fill = mt5.symbol_info(symbol).filling_mode
    if fill & 1: return mt5.ORDER_FILLING_FOK
    if fill & 2: return mt5.ORDER_FILLING_IOC
    return mt5.ORDER_FILLING_RETURN

def calculate_risk_lot(symbol, sl_dist):
    try:
        acc = mt5.account_info()
        risk_val = acc.equity * RISK_PER_POSITION
        tick_val = mt5.symbol_info(symbol).trade_tick_value
        if sl_dist == 0: return MIN_LOT
        raw_lot = risk_val / (sl_dist * tick_val)
        lot = round(raw_lot / POSITIONS_TO_OPEN, 2)
        return max(min(lot, MAX_LOT), MIN_LOT)
    except: return MIN_LOT

def check_recent_win_cooldown(symbol, magic, cooldown_minutes=10):
    """Checks if the last closed burst was a win. If so, returns True to pause."""
    from_date = datetime.now() - timedelta(minutes=cooldown_minutes)
    to_date = datetime.now()
    
    # Get history for this magic number
    history = mt5.history_deals_get(from_date, to_date, group=f"*{symbol}*")
    
    if history:
        # Look at the most recent deal
        last_deal = history[-1]
        # Check if it was a closed position (entry out) and if profit was positive
        if last_deal.entry == mt5.DEAL_ENTRY_OUT:
            if last_deal.profit > 0:
                return True # A win was detected, stay in cooldown
    return False

def sanitize_stops(symbol, order_type, price, sl, tp):
    """
    Adjusts SL/TP to meet broker's minimum distance requirements 
    and normalizes them to the correct number of digits.
    """
    s_info = mt5.symbol_info(symbol)
    if not s_info: return sl, tp
    
    point = s_info.point
    digits = s_info.digits
    
    # 1. Get broker's minimum distance (Stop Level)
    min_dist = max(s_info.trade_stops_level, s_info.trade_freeze_level) * point
    buffer = 2 * point  # Add a 2-point safety buffer for fast markets
    total_min = min_dist + buffer

    # 2. Adjust for Buy Orders
    if order_type == mt5.ORDER_TYPE_BUY:
        if sl > 0 and sl > (price - total_min):
            sl = price - total_min
        if tp > 0 and tp < (price + total_min):
            tp = price + total_min
            
    # 3. Adjust for Sell Orders
    elif order_type == mt5.ORDER_TYPE_SELL:
        if sl > 0 and sl < (price + total_min):
            sl = price + total_min
        if tp > 0 and tp > (price - total_min):
            tp = price - total_min

    # 4. Final Rounding to correct digits
    return round(sl, digits), round(tp, digits)

def sanitize_volume(symbol, requested_lots):
    """
    Adjusts the lot size to be within broker limits and 
    a perfect multiple of the allowed volume step.
    """
    s_info = mt5.symbol_info(symbol)
    if s_info is None:
        return requested_lots

    min_vol = s_info.volume_min
    max_vol = s_info.volume_max
    vol_step = s_info.volume_step

    # 1. Round down to the nearest valid step
    sanitized_vol = math.floor(requested_lots / vol_step) * vol_step
    
    # 2. Force within Min/Max boundaries
    if sanitized_vol < min_vol:
        sanitized_vol = min_vol
    if sanitized_vol > max_vol:
        sanitized_vol = max_vol

    # 3. Final rounding to handle float precision issues
    step_str = str(vol_step).split('.')
    precision = len(step_str[1]) if len(step_str) > 1 else 0
    
    return round(float(sanitized_vol), precision)

def take_partial_profits(symbol, magic, percentage=0.5):
    """Closes a percentage of the volume for all profitable positions."""
    positions = mt5.positions_get(symbol=symbol, magic=magic)
    if not positions:
        return

    # Check if EVERY position is currently in profit
    all_in_profit = all(p.profit > 0 for p in positions)
    
    if all_in_profit:
        s_info = mt5.symbol_info(symbol)
        vol_step = s_info.volume_step
        
        for p in positions:
            # Calculate 50% of the current volume
            raw_partial_vol = p.volume * percentage
            # Sanitize volume to match broker steps
            partial_vol = math.floor(raw_partial_vol / vol_step) * vol_step
            
            if partial_vol < s_info.volume_min:
                continue 

            tick = mt5.symbol_info_tick(symbol)
            order_type = mt5.ORDER_TYPE_SELL if p.type == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY
            price = tick.bid if p.type == mt5.ORDER_TYPE_BUY else tick.ask

            request = {
                "action": mt5.TRADE_ACTION_DEAL,
                "symbol": symbol,
                "volume": float(partial_vol),
                "type": order_type,
                "position": p.ticket,
                "price": price,
                "deviation": 10,
                "magic": magic,
                "comment": "Aron Trader",
                "type_filling": get_filling_mode(symbol),
            }
            
            res = mt5.order_send(request)
            if res.retcode == mt5.TRADE_RETCODE_DONE:
                logger.info(f"Partial TP: Closed {partial_vol} of {p.volume} for ticket {p.ticket}")

def calculate_dynamic_lot(symbol, risk_percent=0.01):
    """Calculates a lot size based on equity."""
    acc = mt5.account_info()
    s_info = mt5.symbol_info(symbol)
    if not acc or not s_info:
        return MIN_LOT

    equity = acc.equity
    dynamic_lot = (equity * risk_percent) 
    
    return sanitize_volume(symbol, dynamic_lot)

# ----------------- NEW LOGIC: SWING POINTS -----------------
def get_swing_points(symbol, timeframe, count=20):
    """Detects recent Swing High and Swing Low."""
    rates = mt5.copy_rates_from_pos(symbol, timeframe, 0, count)
    if rates is None or len(rates) < 5: return None, None
    df = pd.DataFrame(rates)
    swing_high = df['high'].max()
    swing_low = df['low'].min()
    return swing_high, swing_low

# ----------------- M30 MAJOR BIAS LOGIC -----------------
def analyze_m30_macro(symbol):
    """Analyzes M30 structure with Equilibrium (0.5) logic."""
    try:
        rates = mt5.copy_rates_from_pos(symbol, TIMEFRAME_M30, 0, 3)
        if rates is None or len(rates) < 3: return "NEUTRAL"
        
        prev_m30 = rates[1]
        live_m30 = rates[2]
        
        p_high, p_low = prev_m30['high'], prev_m30['low']
        p_mid = (p_high + p_low) / 2
        curr_open, curr_price = live_m30['open'], live_m30['close']
        
        if abs(curr_open - p_mid) < (p_high - p_low) * 0.05:
            m15_rates = mt5.copy_rates_from_pos(symbol, TIMEFRAME_M15, 1, 1) 
            if m15_rates:
                return "UP" if m15_rates[0]['close'] > m15_rates[0]['open'] else "DOWN"

        if curr_price > p_high: return "UP"
        if curr_price < p_low: return "DOWN"
        if curr_price > p_mid: return "UP"
        if curr_price < p_mid: return "DOWN"
        
        return "NEUTRAL"
    except Exception as e:
        logger.error(f"M30 Bias Error: {e}")
        return "NEUTRAL"

# ----------------- CANDLESTICK PATTERN LOGIC -----------------
def get_candle_pattern(rates):
    if rates is None or len(rates) < 2: return "NONE"
    curr, prev = rates[-1], rates[-2]
    body = abs(curr['close'] - curr['open'])
    upper_wick = curr['high'] - max(curr['close'], curr['open'])
    lower_wick = min(curr['close'], curr['open']) - curr['low']
    full_range = max(curr['high'] - curr['low'], 0.001)

    if lower_wick > (2 * body) and upper_wick < (0.1 * full_range): return "HAMMER"
    if upper_wick > (2 * body) and lower_wick < (0.1 * full_range): return "SHOOTING_STAR"
    if curr['close'] > curr['open'] and prev['close'] < prev['open']:
        if curr['close'] > prev['open'] and curr['open'] < prev['close']: return "BULLISH_ENGULFING"
    if curr['close'] < curr['open'] and prev['close'] > prev['open']:
        if curr['close'] < prev['open'] and curr['open'] > prev['close']: return "BEARISH_ENGULFING"
    return "NONE"

# ----------------- TIMEFRAME ALIGNMENT LOGIC -----------------
def is_trend_aligned(symbol):
    try:
        r15 = mt5.copy_rates_from_pos(symbol, TIMEFRAME_M15, 1, 1)
        r5 = mt5.copy_rates_from_pos(symbol, TIMEFRAME_TREND, 1, 1)
        r1 = mt5.copy_rates_from_pos(symbol, TIMEFRAME_EXEC, 1, 1)
        if not all([r1 is not None, r5 is not None, r15 is not None]): return "NEUTRAL"
        m15_up = r15[0]['close'] > r15[0]['open']
        m5_up = r5[0]['close'] > r5[0]['open']
        m1_up = r1[0]['close'] > r1[0]['open']
        if m15_up and m5_up and m1_up: return "UP"
        if not m15_up and not m5_up and not m1_up: return "DOWN"
        return "NEUTRAL"
    except: return "NEUTRAL"

# ----------------- M15 MACRO LOGIC -----------------
def analyze_m15_macro(symbol):
    try:
        rates = mt5.copy_rates_from_pos(symbol, TIMEFRAME_M15, 0, 1)
        if rates is None: return None
        live = rates[0]
        mid = (live['high'] + live['low']) / 2
        bias = "UP" if live['close'] > mid else "DOWN"
        if live['close'] > live['open'] and live['close'] < mid: bias = "UP"
        elif live['close'] < live['open'] and live['close'] > mid: bias = "DOWN"
        return bias
    except: return "NEUTRAL"

# ----------------- CANDLE ANALYSIS -----------------
def analyze_candle_structure(symbol):
    try:
        rates_exec = mt5.copy_rates_from_pos(symbol, TIMEFRAME_EXEC, 0, 4)
        if rates_exec is None or len(rates_exec) < 4: return None
        
        c3 = rates_exec[2]
        c1_up, c2_up, c3_up = rates_exec[0]['close']>rates_exec[0]['open'], rates_exec[1]['close']>rates_exec[1]['open'], c3['close']>c3['open']
        midpoint = (c3['high'] + c3['low']) / 2
        is_trending = (c1_up == c2_up == c3_up)
        
        r15_history = mt5.copy_rates_from_pos(symbol, TIMEFRAME_M15, 0, 2)
        m15_prev = r15_history[0] if r15_history is not None and len(r15_history) > 1 else None

        swing_h, swing_l = get_swing_points(symbol, TIMEFRAME_TREND)

        return {
            "high": c3['high'], "low": c3['low'], "mid": midpoint, 
            "direction": "UP" if c3_up else "DOWN",
            "type": "CONTINUATION" if is_trending else "REVERSAL",
            "live_price": rates_exec[3]['close'],
            "alignment": is_trend_aligned(symbol),
            "m15_bias": analyze_m15_macro(symbol),
            "m15_prev": m15_prev,
            "m30_bias": m30_bias_cache[symbol],
            "swing_h": swing_h, "swing_l": swing_l
        }
    except: return None

# ----------------- POSITION MANAGEMENT -----------------
def manage_active_positions(symbol, magic):
    positions = mt5.positions_get(symbol=symbol, magic=magic)
    if not positions: return
    now = datetime.now().timestamp()
    for pos in positions:
        if pos.profit > 0 and (now - pos.time) >= MIN_HOLD_TIME:
            close_position(symbol, pos, "PROFIT_EXIT")

def close_position(symbol, pos, reason):
    tick = mt5.symbol_info_tick(symbol)
    order_type = mt5.ORDER_TYPE_SELL if pos.type == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY
    price = tick.bid if order_type == mt5.ORDER_TYPE_SELL else tick.ask
    request = {
        "action": mt5.TRADE_ACTION_DEAL, "symbol": symbol, "volume": pos.volume,
        "type": order_type, "position": pos.ticket, "price": price,
        "magic": pos.magic, "comment": f"Close {reason}", 
        "type_filling": get_filling_mode(symbol)
    }
    mt5.order_send(request)

# ----------------- TRADE EXECUTION -----------------
def place_trade_burst(symbol, magic, order_type, lots, sl, tp, comment="Aron Trader"):
    s_info = mt5.symbol_info(symbol)
    if s_info is None:
        logger.error(f"{symbol} not found")
        return

    tick = mt5.symbol_info_tick(symbol)
    point = s_info.point
    digits = s_info.digits
    
    vol_min = s_info.volume_min
    vol_max = s_info.volume_max
    vol_step = s_info.volume_step
    
    final_lots = math.floor(float(lots) / vol_step) * vol_step
    
    if final_lots < vol_min: final_lots = vol_min
    if final_lots > vol_max: final_lots = vol_max
    
    step_str = str(vol_step).split('.')
    v_precision = len(step_str[1]) if len(step_str) > 1 else 0
    final_lots = round(final_lots, v_precision)
    
    spread = (tick.ask - tick.bid) / point
    if spread > MAX_SPREAD_POINTS:
        logger.warning(f"Spread too high for {symbol}: {spread}")
        return

    stop_level = s_info.trade_stops_level * point
    freeze_level = s_info.trade_freeze_level * point
    
    buffer = (20 * point) if digits == 5 else (2 * point)
    min_dist = max(stop_level, freeze_level) + buffer

    for _ in range(POSITIONS_TO_OPEN):
        t = mt5.symbol_info_tick(symbol)
        if t is None: continue
        
        price = t.ask if order_type == mt5.ORDER_TYPE_BUY else t.bid
        final_sl = float(sl)
        final_tp = float(tp)

        if order_type == mt5.ORDER_TYPE_BUY:
            if final_sl > (t.bid - min_dist):
                final_sl = t.bid - min_dist
            if final_tp < (t.ask + min_dist):
                final_tp = t.ask + min_dist
        else:
            if final_sl < (t.ask + min_dist):
                final_sl = t.ask + min_dist
            if final_tp > (t.bid - min_dist):
                final_tp = t.bid - min_dist

        final_sl = round(final_sl, digits)
        final_tp = round(final_tp, digits)
        price = round(price, digits)

        request = {
            "action": mt5.TRADE_ACTION_DEAL,
            "symbol": symbol,
            "volume": final_lots,
            "type": order_type,
            "price": price,
            "sl": final_sl,
            "tp": final_tp,
            "magic": int(magic),
            "comment": comment,
            "type_filling": get_filling_mode(symbol),
            "deviation": 10
        }
        
        res = mt5.order_send(request)
        if res.retcode != mt5.TRADE_RETCODE_DONE:
            print(f"Execution Failed: {res.retcode} - {res.comment} | FAILED: {symbol} SL: {final_sl} Price: {price} Vol: {final_lots}")
        else:
            logger.info(f"Burst Order Successful: {symbol} @ {price} | Vol: {final_lots}")

def scalp_logic(symbol, magic, analysis):
    if datetime.now() < symbol_cooldowns[symbol] + timedelta(seconds=COOLDOWN_SECONDS): return
    if mt5.positions_get(symbol=symbol, magic=magic): return

    if check_recent_win_cooldown(symbol, magic, cooldown_minutes=10):
        return
  
    live_p, m30_bias = analysis['live_price'], analysis['m30_bias']
    
    if analysis.get('m15_prev'):
        p_h, p_l = analysis['m15_prev']['high'], analysis['m15_prev']['low']
        threshold = (p_h - p_l) * 0.10
        if (p_h - live_p) < threshold and live_p < p_h and m30_bias == "DOWN":
            lots = calculate_risk_lot(symbol, abs(live_p - p_h))
            place_trade_burst(symbol, magic, mt5.ORDER_TYPE_SELL, lots, p_h, (p_h+p_l)/2)
            symbol_cooldowns[symbol] = datetime.now()
            return
        if (live_p - p_l) < threshold and live_p > p_l and m30_bias == "UP":
            lots = calculate_risk_lot(symbol, abs(live_p - p_l))
            place_trade_burst(symbol, magic, mt5.ORDER_TYPE_BUY, lots, p_l, (p_h+p_l)/2)
            symbol_cooldowns[symbol] = datetime.now()
            return

    if analysis['type'] == "CONTINUATION" and analysis['alignment'] == m30_bias:
        if analysis['direction'] == "UP" and analysis['m15_bias'] == "UP" and live_p > analysis['mid']:
            if analysis['swing_h'] and live_p < analysis['swing_h']:
                sl = analysis['low']
                lots = calculate_risk_lot(symbol, abs(live_p - sl))
                tp = live_p + (abs(live_p - sl) * TP_MULTIPLIER)
                place_trade_burst(symbol, magic, mt5.ORDER_TYPE_BUY, lots, sl, tp)
                symbol_cooldowns[symbol] = datetime.now()
        elif analysis['direction'] == "DOWN" and analysis['m15_bias'] == "DOWN" and live_p < analysis['mid']:
            if analysis['swing_l'] and live_p > analysis['swing_l']:
                sl = analysis['high']
                lots = calculate_risk_lot(symbol, abs(live_p - sl))
                tp = live_p - (abs(live_p - sl) * TP_MULTIPLIER)
                place_trade_burst(symbol, magic, mt5.ORDER_TYPE_SELL, lots, sl, tp)
                symbol_cooldowns[symbol] = datetime.now()

def display_dashboard(acc):
    """Prints a clean dashboard in the console."""
    os.system('cls' if os.name == 'nt' else 'clear')
    print("="*50)
    print(f" LIVE TRADING MONITOR - {datetime.now().strftime('%H:%M:%S')} ")
    print("="*50)
    if acc:
        print(f"Equity: {acc.equity:.2f} | Balance: {acc.balance:.2f}")
        print(f"Current Profit: {acc.profit:.2f}")
        print(f"Target: {DAILY_PROFIT_TARGET} | Limit: {DAILY_LOSS_LIMIT}")
    print("-" * 50)
    print(f"{'Symbol':<20} | {'M30 Bias':<10} | {'Status':<15}")
    for s in SYMBOLS:
        bias = m30_bias_cache.get(s, "WAITING")
        print(f"{s:<20} | {bias:<10} | ACTIVE")
    print("="*50)

def close_partial_with_filling(symbol, position, volume, magic):
    """Helper to handle partial closes with correct filling modes."""
    tick = mt5.symbol_info_tick(symbol)
    order_type = mt5.ORDER_TYPE_SELL if position.type == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY
    
    request = {
        "action": mt5.TRADE_ACTION_DEAL,
        "symbol": symbol,
        "volume": float(volume),
        "type": order_type,
        "position": position.ticket,
        "price": tick.bid if order_type == mt5.ORDER_TYPE_SELL else tick.ask,
        "magic": magic,
        "comment": "Aron Trader",
        "type_time": mt5.ORDER_TIME_GTC,
        "type_filling": mt5.ORDER_FILLING_IOC, 
    }
    result = mt5.order_send(request)
    return result

# ----------------- PRECIOUS METALS SCALING LOGIC -----------------
def execute_crash_scaling(symbol, magic, analysis, acc):
    current_time = datetime.now()
    price = analysis['live_price']

    # Trailing distance adjusted for Gold/Silver volatility
    trail_dist = price * 0.005  
    trail_step = price * 0.001  

    # Logic updated for XAUUSD / XAGUSD
    if symbol in ["XAUUSD", "XAGUSD"]:
        
        # 1. DAILY TRADE LIMIT CHECK (Max 55)
        start_of_day = datetime(current_time.year, current_time.month, current_time.day)
        history_deals = mt5.history_deals_get(start_of_day, current_time, group=f"*{symbol}*")
        
        trade_count = 0
        if history_deals:
            trade_count = len([d for d in history_deals if d.magic == magic and d.entry == mt5.DEAL_ENTRY_IN])

        if trade_count >= 55:
            can_enter = False
        else:
            can_enter = True

        # 2. H4 REFERENCE ANALYSIS
        rates_h4 = mt5.copy_rates_from_pos(symbol, mt5.TIMEFRAME_H4, 1, 1)
        if rates_h4 is None or len(rates_h4) == 0: 
            return False
            
        prev_h4 = rates_h4[0]
        h4_high, h4_low = prev_h4['high'], prev_h4['low']
        h4_mid = (h4_high + h4_low) / 2

        # --- RANGE FILTER ---
        hist_h4 = mt5.copy_rates_from_pos(symbol, mt5.TIMEFRAME_H4, 1, 10)
        if hist_h4 is not None and len(hist_h4) > 0:
            avg_h4_vol = sum(x['high'] - x['low'] for x in hist_h4) / len(hist_h4)
            if (h4_high - h4_low) < (avg_h4_vol * 0.6):
                can_enter = False 
        
        positions = mt5.positions_get(symbol=symbol, magic=magic) or []

        # 3. ENTRY LOGIC: CISD + FRACTAL / EXPANSION (M15)
        if not positions and can_enter:
            rates_m15 = mt5.copy_rates_from_pos(symbol, mt5.TIMEFRAME_M15, 0, 2)
            if rates_m15 is not None and len(rates_m15) >= 2:
                curr_m15 = rates_m15[1]
                prev_m15 = rates_m15[0]
                
                direction = None
                
                # --- SCENARIO A: BUYING THE TOP ---
                if price > h4_high and curr_m15['close'] > prev_m15['open'] and prev_m15['close'] < prev_m15['open']:
                    direction = mt5.ORDER_TYPE_BUY
                    sl = h4_mid
                    tp = price + (price - sl) * 1.5

                # --- SCENARIO B: SELLING THE BOTTOM ---
                elif price < h4_low and curr_m15['close'] < prev_m15['open'] and prev_m15['close'] > prev_m15['open']:
                    direction = mt5.ORDER_TYPE_SELL
                    sl = h4_mid
                    tp = price - (sl - price) * 1.5

                # --- SCENARIO C: STANDARD REVERSAL ---
                elif price < h4_mid and curr_m15['close'] > prev_m15['open'] and prev_m15['close'] < prev_m15['open']:
                    direction = mt5.ORDER_TYPE_BUY
                    sl = h4_low - (h4_high - h4_low) * 0.05
                    tp = price + (price - sl) * 2
                
                elif price > h4_mid and curr_m15['close'] < prev_m15['open'] and prev_m15['close'] > prev_m15['open']:
                    direction = mt5.ORDER_TYPE_SELL
                    sl = h4_high + (h4_high - h4_low) * 0.05
                    tp = price - (sl - price) * 2

                if direction is not None:
                    # Lot size tailored for metal accounts (starting at 0.01)
                    lot = max(MIN_LOT, round((acc.equity * 0.00001), 2))
                    needed_margin = mt5.order_calc_margin(direction, symbol, lot, price)
                    if needed_margin and acc.margin_free * 0.9 > needed_margin:
                        place_trade_burst(symbol, magic, direction, lot, sl, tp)

        # 4. POSITION MANAGEMENT
        positions = mt5.positions_get(symbol=symbol, magic=magic) or []
        for pos in positions:
            open_p, current_sl = pos.price_open, pos.sl
            profit_dist = abs(pos.tp - open_p)
            current_gain = abs(price - open_p)
            
            # Trailing Stop Logic
            if pos.type == mt5.ORDER_TYPE_BUY:
                new_trail_sl = price - trail_dist
                if new_trail_sl > current_sl + trail_step:
                    mt5.order_send({"action": mt5.TRADE_ACTION_SLTP, "position": pos.ticket, "sl": new_trail_sl, "tp": pos.tp})
            
            elif pos.type == mt5.ORDER_TYPE_SELL:
                new_trail_sl = price + trail_dist
                if current_sl == 0 or new_trail_sl < current_sl - trail_step:
                    mt5.order_send({"action": mt5.TRADE_ACTION_SLTP, "position": pos.ticket, "sl": new_trail_sl, "tp": pos.tp})

            # Partial & BE Logic
            if current_gain >= (profit_dist * 0.5) and pos.volume > MIN_LOT:
                partial_vol = round(pos.volume * 0.75, 2)
                if partial_vol >= MIN_LOT:
                    close_partial_with_filling(symbol, pos, partial_vol, magic)
                    
            if current_gain >= (profit_dist * 0.25):
                new_sl = open_p
                if abs(new_sl - current_sl) > 0.001:
                    mt5.order_send({"action": mt5.TRADE_ACTION_SLTP, "position": pos.ticket, "sl": new_sl, "tp": pos.tp})
        
        return True

    return False

# ----------------- PASSKEY & MAIN -----------------
PASSKEY_FILE = "bot_access.json"
CORRECT_PASSKEY = "1234567890#12345678901#"
system_id = platform.node() + "_" + platform.system() + "_" + platform.release()
access_granted = False
if os.path.exists(PASSKEY_FILE):
    try:
        with open(PASSKEY_FILE, "r") as f:
            if json.load(f).get(system_id) == CORRECT_PASSKEY: access_granted = True
    except: pass
if not access_granted:
    if input("Enter bot passkey: ") == CORRECT_PASSKEY:
        with open(PASSKEY_FILE, "w") as f: json.dump({system_id: CORRECT_PASSKEY}, f)
    else: exit()

def main():
    if not initialize_mt5(): return
    magics = [MAGIC_BASE + i for i in range(len(SYMBOLS))]
    last_m30_check = 0
    
    try:
        while True:
            acc = mt5.account_info()
            if not acc:
                time.sleep(1); continue

            if acc.profit >= DAILY_PROFIT_TARGET or acc.profit <= DAILY_LOSS_LIMIT:
                print(f"--- TARGET REACHED: {acc.profit} ---")
                time.sleep(60); continue

            os.system('cls' if os.name == 'nt' else 'clear')
            print("="*75)
            print(f" ARON TRADER | {datetime.now().strftime('%H:%M:%S')} | EQUITY: {acc.equity} | PROFIT: {acc.profit}")
            print("="*75)
            print(f"{'SYMBOL':<20} | {'M30 BIAS':<8} | {'SPREAD':<6} | {'SWING H/L':<15} | {'PRICE'}")
            print("-" * 75)

            curr_t = time.time()
            if curr_t - last_m30_check >= M30_UPDATE_INTERVAL:
                for s in SYMBOLS: m30_bias_cache[s] = analyze_m30_macro(s)
                last_m30_check = curr_t
            
            for i, s in enumerate(SYMBOLS):
                analysis = analyze_candle_structure(s)
                if analysis:
                    # 1. INITIAL SCALING CHECK
                    in_range = (10 <= acc.equity <= 50000)
                    is_scaling_symbol = s in ["XAUUSD", "XAGUSD"]
                    
                    is_scaling = False # Default

                    # 2. DECISION GATE
                    if in_range:
                        if is_scaling_symbol:
                            is_scaling = execute_crash_scaling(s, magics[i], analysis, acc)
                        else:
                            continue 
                    
                    # 3. FALLBACK / NORMAL LOGIC
                    if not is_scaling:
                        take_partial_profits(s, magics[i])
                        manage_active_positions(s, magics[i])
                        scalp_logic(s, magics[i], analysis)

                    # 4. DASHBOARD UPDATE
                    in_win_pause = check_recent_win_cooldown(s, magics[i], 10)
                    pause_status = "⏸️ WIN PAUSE" if in_win_pause else ("🚀 SCALING" if is_scaling else "✅ ACTIVE")
                    
                    s_info = mt5.symbol_info(s)
                    tick = mt5.symbol_info_tick(s)
                    live_spread = (tick.ask - tick.bid) / s_info.point if s_info else 0
                    
                    swing_info = f"{analysis['swing_h']:.2f}/{analysis['swing_l']:.2f}"
                    spread_status = "✅" if live_spread <= MAX_SPREAD_POINTS else "❌"
                    
                    print(f"{s:<20} | {analysis['m30_bias']:<8} | {live_spread:>4.0f} {spread_status} | {swing_info:<15} | {pause_status} | {analysis['live_price']}")
            
            print("="*75)
            time.sleep(SLEEP_INTERVAL)
    except Exception as e:
        print(f"Main Loop Error: {e}")

    except KeyboardInterrupt:
        logger.info("Manual stop detected.")
    finally:
        mt5.shutdown()
        logger.info("MT5 connection closed.")

if __name__ == "__main__":
    main()