# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 1 ── IMPORTS, CONSTANTS & GLOBAL CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

import os, json, time, math, random, sqlite3, logging, warnings, gc
import datetime, traceback, hashlib, re, io, csv, threading, secrets, hmac
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any, Union
from collections import defaultdict

# ── bcrypt (preferred password hashing — pip install bcrypt)
try:
    import bcrypt as _bcrypt  # type: ignore
    BCRYPT_AVAILABLE = True
except ImportError:
    BCRYPT_AVAILABLE = False

warnings.filterwarnings("ignore")
os.environ["TF_CPP_MIN_LOG_LEVEL"] = "3"

import streamlit as st
import streamlit.components.v1 as components

# ── requests / BS4
try:
    import requests
    from bs4 import BeautifulSoup
    BS4_AVAILABLE = True
except ImportError:
    BS4_AVAILABLE = False

# ── NumPy
try:
    import numpy as np
    NP_AVAILABLE = True
except ImportError:
    NP_AVAILABLE = False
    class np:  # type: ignore[no-redef]
        @staticmethod
        def array(x, **kw): return list(x)
        @staticmethod
        def mean(x): return sum(x) / max(len(x), 1)
        @staticmethod
        def std(x):
            mu = sum(x) / max(len(x), 1)
            return math.sqrt(sum((v - mu) ** 2 for v in x) / max(len(x), 1))
        @staticmethod
        def argmax(x): return x.index(max(x)) if hasattr(x, "index") else 0
        float32 = float

# ── TensorFlow / Keras — LAZY IMPORT (saves ~500 MB RAM on startup)
# TF is only loaded when LSTM training is actually triggered.
TF_AVAILABLE = False  # will be set True on first successful lazy import

def _try_import_tf():
    """Lazy-import TensorFlow. Returns True on success."""
    global TF_AVAILABLE
    if TF_AVAILABLE:
        return True
    try:
        import tensorflow as tf  # type: ignore  # noqa: F401
        from tensorflow.keras.models import Sequential  # type: ignore  # noqa: F401
        from tensorflow.keras.layers import LSTM, Dense, Dropout  # type: ignore  # noqa: F401
        from tensorflow.keras.optimizers import Adam  # type: ignore  # noqa: F401
        # Inject into module globals so existing code can reference them
        import sys
        _m = sys.modules[__name__]
        setattr(_m, 'tf', tf)
        setattr(_m, 'Sequential', Sequential)
        setattr(_m, 'LSTM', LSTM)
        setattr(_m, 'Dense', Dense)
        setattr(_m, 'Dropout', Dropout)
        setattr(_m, 'Adam', Adam)
        TF_AVAILABLE = True
        return True
    except ImportError:
        return False

# ── OpenAI-compatible client (used for Grok xAI)
try:
    from openai import OpenAI as _OpenAI  # type: ignore
    OPENAI_SDK = True
except ImportError:
    OPENAI_SDK = False

# ── Groq SDK fallback
try:
    from groq import Groq as _Groq  # type: ignore
    GROQ_SDK = True
except ImportError:
    GROQ_SDK = False

# ── NetworkX
try:
    import networkx as nx  # type: ignore
    NX_AVAILABLE = True
except ImportError:
    NX_AVAILABLE = False

# ── Pandas
try:
    import pandas as pd
    PANDAS_AVAILABLE = True
except ImportError:
    PANDAS_AVAILABLE = False

# ── PyDeck (WebGL-powered 3D map renderer — Uber Deck.gl)
try:
    import pydeck as pdk  # type: ignore
    PYDECK_AVAILABLE = True
except ImportError:
    PYDECK_AVAILABLE = False

# ── polyline decoder (OSRM route geometry)
try:
    import polyline as _polyline_lib  # type: ignore
    POLYLINE_AVAILABLE = True
except ImportError:
    POLYLINE_AVAILABLE = False

# ── GeoPandas + Shapely (Point-in-Polygon zone analysis)
try:
    import geopandas as gpd       # type: ignore
    from shapely.geometry import Point, Polygon  # type: ignore
    GEOPANDAS_AVAILABLE = True
except ImportError:
    GEOPANDAS_AVAILABLE = False

# ── dotenv
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass

# ── Page config — MUST be first st.* call
st.set_page_config(
    page_title="LOGIX — Supply Chain Intelligence",
    page_icon="🚀",
    layout="wide",
    initial_sidebar_state="expanded",
)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s — %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("LogixApp")

# ══════════════════════════════════════════════════════════════════════════════
# GLOBAL CONSTANTS
# ══════════════════════════════════════════════════════════════════════════════

APP_VERSION   = "7.2.0"
APP_NAME      = "LOGIX"
DEVELOPER     = "Sourab Dey Soptom"
DB_PATH       = "logix_v7.db"
SCRAPE_TTL    = 600            # 10-min cache
FORECAST_DAYS = 7
CHALDAL_BASE  = "https://chaldal.com"

# ═══════════════════════════════════════════════════════════════════════════════
# RBAC — ROLE DEFINITIONS & TAB ACCESS MATRIX
# ═══════════════════════════════════════════════════════════════════════════════

# All available tabs in display order (index matches tabs list in render())
ALL_TABS = [
    "🏠 Command Centre",   # 0
    "📦 Inventory",        # 1
    "🧠 AI Intelligence",  # 2
    "⚖️ DSS Engine",       # 3
    "🗺️ Live Map",         # 4
    "🚚 Logistics",        # 5
    "💰 Finance",          # 6
    "🔔 Alerts",           # 7
    "📋 AI Logs",          # 8
    "⚙️ Settings",         # 9
]

# Role → list of tab indices accessible
ROLE_TAB_ACCESS: Dict[str, List[int]] = {
    "admin":      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],   # All tabs
    "manager":    [0, 1, 2, 3, 7],                    # Cmd + Inv + AI + DSS + Alerts
    "dispatcher": [4, 5],                              # Live Map + Logistics only
}

# Role display labels & badge colours
ROLE_META: Dict[str, Dict[str, str]] = {
    "admin":      {"label": "Super Admin",  "color": "#ff3366"},
    "manager":    {"label": "Manager",      "color": "#ffbb00"},
    "dispatcher": {"label": "Dispatcher",   "color": "#00cfff"},
}

# Session state key for auth context
_AUTH_KEY = "__logix_auth__"

# ── Grok xAI API
# ── Grok xAI API key — secure fallback chain
def _load_grok_api_key() -> str:
    key = os.getenv("GROK_API_KEY")
    if key:
        return key
    try:
        return st.secrets["GROK_API_KEY"]
    except (KeyError, FileNotFoundError):
        return ""

GROK_API_KEY  = _load_grok_api_key()
GROK_BASE_URL = "https://api.x.ai/v1"
GROK_MODEL    = "grok-3-mini"
GROQ_MODEL    = "llama-3.1-8b-instant"



# ── SKU catalogue
SKUS: Dict[str, Tuple[str, str]] = {
    "onion_kg":   ("Onion",              "Vegetables"),
    "potato_kg":  ("Potato",             "Vegetables"),
    "rice_5kg":   ("Rice (5 kg)",        "Staples"),
    "chicken_kg": ("Chicken",            "Meat"),
    "egg_12":     ("Eggs (12 pcs)",      "Protein"),
    "tomato_kg":  ("Tomato",             "Vegetables"),
    "lentil_kg":  ("Red Lentil",         "Staples"),
    "oil_1l":     ("Soybean Oil 1 L",    "Cooking"),
    "flour_kg":   ("Flour (Atta 1 kg)",  "Staples"),
    "sugar_kg":   ("Sugar",              "Staples"),
}

# ── Reference prices (used only when ALL scraping methods fail)
REFERENCE_PRICES: Dict[str, Dict[str, Any]] = {
    "onion_kg":   {"price": 50,  "unit": "kg",       "url_path": "Onion"},
    "potato_kg":  {"price": 50,  "unit": "kg",       "url_path": "Potato"},
    "rice_5kg":   {"price": 345, "unit": "5 kg bag", "url_path": "Rice"},
    "chicken_kg": {"price": 235, "unit": "kg",       "url_path": "Chicken"},
    "egg_12":     {"price": 150, "unit": "dozen",    "url_path": "Egg"},
    "tomato_kg":  {"price": 85,  "unit": "kg",       "url_path": "Tomato"},
    "lentil_kg":  {"price": 135, "unit": "kg",       "url_path": "Lentil"},
    "oil_1l":     {"price": 175, "unit": "litre",    "url_path": "Oil"},
    "flour_kg":   {"price": 58,  "unit": "kg",       "url_path": "Flour"},
    "sugar_kg":   {"price": 130, "unit": "kg",       "url_path": "Sugar"},
}

# ── Dhaka delivery hub coordinates (lat, lon)
DHAKA_HUBS: Dict[str, Tuple[float, float]] = {
    "Gulshan":     (23.7925, 90.4078),
    "Dhanmondi":   (23.7461, 90.3742),
    "Mirpur":      (23.8223, 90.3654),
    "Uttara":      (23.8759, 90.3795),
    "Motijheel":   (23.7330, 90.4176),
    "Mohakhali":   (23.7799, 90.4042),
    "Badda":       (23.7779, 90.4292),
    "Rayer Bazar": (23.7502, 90.3564),
    "Wari":        (23.7214, 90.4179),
}

# ── Road-network edges: (hub_a, hub_b, km, traffic_multiplier)
HUB_EDGES: List[Tuple[str, str, float, float]] = [
    ("Gulshan",     "Mohakhali",   3.5,  1.1),
    ("Gulshan",     "Uttara",      10.2, 1.3),
    ("Gulshan",     "Badda",       3.1,  1.2),
    ("Gulshan",     "Motijheel",   5.0,  1.5),
    ("Mohakhali",   "Mirpur",      6.8,  1.4),
    ("Mohakhali",   "Dhanmondi",   7.1,  1.5),
    ("Mohakhali",   "Badda",       3.9,  1.3),
    ("Mirpur",      "Uttara",      7.5,  1.2),
    ("Mirpur",      "Rayer Bazar", 4.2,  1.3),
    ("Mirpur",      "Dhanmondi",   8.0,  1.4),
    ("Dhanmondi",   "Motijheel",   5.4,  1.6),
    ("Dhanmondi",   "Rayer Bazar", 3.8,  1.2),
    ("Motijheel",   "Wari",        1.8,  1.4),
    ("Motijheel",   "Uttara",      14.5, 2.0),
    ("Wari",        "Motijheel",   1.8,  1.4),
    ("Badda",       "Gulshan",     3.1,  1.2),
    ("Rayer Bazar", "Dhanmondi",   3.8,  1.2),
]

# ── Market event demand multipliers
EVENT_DEMAND_FACTORS: Dict[str, Dict[str, float]] = {
    "Normal Day": {s: 1.0 for s in SKUS},
    "Eid ul-Fitr": {
        "onion_kg": 1.8, "chicken_kg": 2.5, "egg_12": 1.6, "rice_5kg": 1.4,
        "oil_1l": 1.5, "sugar_kg": 2.0, "potato_kg": 1.3, "tomato_kg": 1.2,
        "lentil_kg": 1.4, "flour_kg": 1.7,
    },
    "Puja Festival": {
        "onion_kg": 1.4, "potato_kg": 1.6, "rice_5kg": 1.3, "tomato_kg": 1.5,
        "lentil_kg": 1.5, "flour_kg": 1.4, "sugar_kg": 1.8, "egg_12": 1.2,
        "oil_1l": 1.4, "chicken_kg": 0.9,
    },
    "Hartaal Strike": {s: 0.4 for s in SKUS},
    "Heavy Monsoon": {
        "onion_kg": 0.7, "potato_kg": 1.2, "rice_5kg": 1.5, "lentil_kg": 1.8,
        "tomato_kg": 0.6, "chicken_kg": 0.8, "egg_12": 1.3, "oil_1l": 1.1,
        "flour_kg": 1.2, "sugar_kg": 1.1,
    },
    "IPL / Cricket Match": {
        "onion_kg": 1.1, "potato_kg": 1.2, "egg_12": 1.4, "chicken_kg": 1.5,
        "tomato_kg": 1.1, "rice_5kg": 1.0, "lentil_kg": 1.0, "oil_1l": 1.2,
        "flour_kg": 1.1, "sugar_kg": 1.1,
    },
    "Dhaka Flood": {
        "rice_5kg": 2.0, "lentil_kg": 1.9, "potato_kg": 1.6, "onion_kg": 0.5,
        "tomato_kg": 0.4, "chicken_kg": 0.5, "egg_12": 1.7, "oil_1l": 1.5,
        "flour_kg": 1.8, "sugar_kg": 1.4,
    },
}

# ── DSS default weights
DEFAULT_DSS_WEIGHTS: Dict[str, float] = {
    "demand_score": 0.30,
    "price_score":  0.20,
    "stock_score":  0.25,
    "expiry_score": 0.15,
    "margin_score": 0.10,
}

# ── Chaldal category API endpoints and search terms
CHALDAL_SEARCH_TERMS: Dict[str, List[str]] = {
    "onion_kg":   ["onion", "পেঁয়াজ"],
    "potato_kg":  ["potato", "আলু"],
    "rice_5kg":   ["minicate rice 5kg", "rice 5 kg", "miniket"],
    "chicken_kg": ["broiler chicken", "chicken"],
    "egg_12":     ["egg 12", "eggs 12 pieces"],
    "tomato_kg":  ["tomato", "টমেটো"],
    "lentil_kg":  ["red lentil", "masoor dal", "মসুর"],
    "oil_1l":     ["soybean oil 1 liter", "soya bean oil 1l"],
    "flour_kg":   ["atta 1kg", "flour 1 kg", "আটা"],
    "sugar_kg":   ["sugar 1 kg", "চিনি"],
}

# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 2 ── DATA INGESTION & PERSISTENCE LAYER
# ═══════════════════════════════════════════════════════════════════════════════

class LiveDataScraper:
    """
    Real-time data acquisition engine.

    Data Strategy (multi-method, ordered by reliability):
    ──────────────────────────────────────────────────────
    1. DummyJSON Groceries API  → GET /products/category/groceries
    2. DummyJSON Multi-category → GET /products/category/<cat> for broader coverage
    3. DummyJSON Search API     → GET /products/search?q=<term> per unresolved SKU
    4. Last-known-good cache    → return most recent successful data
    5. Reference prices         → static baseline (labelled "reference")

    Price localisation: DummyJSON prices are in USD. A fixed BDT conversion
    factor (USD_TO_BDT) is applied, then clamped within ±40 % of the curated
    REFERENCE_PRICES to prevent unrealistic outliers.
    """

    # ── Class-level shared state (survives Streamlit reruns) ──────────────────
    _price_cache:   Dict[str, Any] = {}
    _price_ts:      float          = 0.0
    _last_good:     Dict[str, Any] = {}
    _weather_cache: Optional[Dict] = None
    _weather_ts:    float          = 0.0

    # ── DummyJSON catalogue endpoints ─────────────────────────────────────────
    _DUMMYJSON_BASE    = "https://dummyjson.com"
    _DUMMYJSON_CATS    = ["groceries", "vegetables", "dairy", "beverages"]
    _USD_TO_BDT        = 110.0          # approximate conversion rate
    _PRICE_CLAMP_BAND  = 0.40           # allow ±40 % deviation from reference

    # ── Keyword-to-SKU affinity map (ordered from most-specific to least) ─────
    _SKU_KEYWORDS: Dict[str, List[str]] = {
        "onion_kg":   ["onion"],
        "potato_kg":  ["potato", "fries"],
        "rice_5kg":   ["rice", "basmati", "jasmine", "grain"],
        "chicken_kg": ["chicken", "poultry", "broiler", "hen"],
        "egg_12":     ["egg", "eggs"],
        "tomato_kg":  ["tomato", "tomatoes", "ketchup"],
        "lentil_kg":  ["lentil", "lentils", "dal", "pulse", "legume", "chickpea", "bean"],
        "oil_1l":     ["oil", "soybean", "sunflower", "canola", "olive", "cooking oil"],
        "flour_kg":   ["flour", "wheat", "atta", "maida", "cornmeal"],
        "sugar_kg":   ["sugar", "sweetener", "cane", "molasses"],
    }

    # ── Availability normalisation ─────────────────────────────────────────────
    _STOCK_STATUS_MAP: Dict[str, str] = {
        "in stock":        "In Stock",
        "low stock":       "Low Stock",
        "out of stock":    "Out of Stock",
        "limited":         "Low Stock",
        "available":       "In Stock",
        "unavailable":     "Out of Stock",
    }

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)
        self._session: Optional[Any] = None
        if BS4_AVAILABLE:
            self._session = requests.Session()
            self._session.headers.update({
                "User-Agent":      (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/124.0.0.0 Safari/537.36"
                ),
                "Accept":          "application/json",
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
            })

    # ── Public API ────────────────────────────────────────────────────────────

    def fetch_chaldal_prices(self) -> Dict[str, Dict]:
        """
        Fetch live grocery prices via DummyJSON public API.
        Returns: sku_id → {price, prev_price, stock, name, category, unit, data_source}
        """
        now = time.time()
        if now - self._price_ts < SCRAPE_TTL and self._price_cache:
            return self._price_cache

        result: Dict[str, Dict] = {}
        source = "reference"

        if BS4_AVAILABLE and self._session:
            # ── Method 1: bulk category fetch ─────────────────────────────────
            all_products: List[Dict] = []
            try:
                all_products = self._fetch_all_category_products()
                if all_products:
                    self.logger.info(
                        "DummyJSON category sweep: %d products fetched", len(all_products)
                    )
            except Exception as exc:
                self.logger.warning("DummyJSON category fetch failed: %s", exc)

            # ── Method 2: targeted per-SKU search for remaining gaps ──────────
            result = self._map_products_to_skus(all_products)
            unresolved = [s for s in SKUS if s not in result]
            if unresolved:
                try:
                    search_result = self._fetch_via_search(unresolved)
                    result.update(search_result)
                    self.logger.info(
                        "DummyJSON search filled %d additional SKUs", len(search_result)
                    )
                except Exception as exc:
                    self.logger.warning("DummyJSON search fallback failed: %s", exc)

            if len(result) >= 5:
                source = "live_api"
            elif len(result) >= 2:
                source = "live_search"

        # ── Method 3: last-known-good cache ───────────────────────────────────
        if len(result) < 3 and self._last_good:
            result = {k: dict(v) for k, v in self._last_good.items()}
            source = "cached"
            self.logger.info("Falling back to last-known-good cache (%d SKUs)", len(result))

        # ── Method 4: reference prices (clearly labelled) ─────────────────────
        for sku_id in SKUS:
            if sku_id not in result:
                ref = REFERENCE_PRICES.get(sku_id, {})
                result[sku_id] = {
                    "price":      float(ref.get("price", 0)),
                    "prev_price": float(ref.get("price", 0)),
                    "stock":      "Unknown",
                    "source":     "reference",
                }

        # ── Enrich every SKU with static metadata ─────────────────────────────
        for sku_id, (sku_name, sku_cat) in SKUS.items():
            if sku_id in result:
                entry = result[sku_id]
                entry.setdefault("name",     sku_name)
                entry.setdefault("category", sku_cat)
                entry.setdefault("unit",     REFERENCE_PRICES.get(sku_id, {}).get("unit", ""))
                entry["data_source"] = entry.get("source", source)

        # ── Persist to class-level cache ──────────────────────────────────────
        LiveDataScraper._price_cache = result
        LiveDataScraper._price_ts    = now
        if source in ("live_api", "live_search"):
            LiveDataScraper._last_good = {k: dict(v) for k, v in result.items()}

        # Free any intermediate objects and help GC reclaim RAM
        gc.collect()
        return result

    def fetch_weather_data(self) -> Dict[str, Any]:
        """Fetch current Dhaka weather from wttr.in (JSON feed)."""
        now = time.time()
        if now - self._weather_ts < SCRAPE_TTL and self._weather_cache:
            return self._weather_cache

        data = self._call_wttr_api()
        LiveDataScraper._weather_cache = data
        LiveDataScraper._weather_ts    = now
        return data

    def force_refresh(self) -> None:
        """Invalidate all in-memory caches and force a full re-fetch."""
        LiveDataScraper._price_ts   = 0.0
        LiveDataScraper._weather_ts = 0.0
        self.logger.info("LiveDataScraper: all caches invalidated")

    def get_data_source_label(self) -> str:
        """Return a human-readable badge for the current data source."""
        if not self._price_cache:
            return "No data yet"
        sources = {v.get("data_source", "?") for v in self._price_cache.values()}
        src = sources.pop() if len(sources) == 1 else "mixed"
        labels: Dict[str, str] = {
            "live_api":    "🟢 Live (DummyJSON API)",
            "live_search": "🟢 Live (DummyJSON Search)",
            "cached":      "🟡 Cached (last good)",
            "reference":   "🔴 Reference (offline baseline)",
            "mixed":       "🟡 Mixed sources",
        }
        return labels.get(src, src)

    # ── Private: DummyJSON data fetching ──────────────────────────────────────

    def _fetch_all_category_products(self) -> List[Dict]:
        """
        Sweep every category in _DUMMYJSON_CATS and return a deduplicated
        product list.  DummyJSON is paginated at 30 items; we request limit=100
        to capture the full catalogue in one call per category.
        """
        seen_ids: set = set()
        all_products: List[Dict] = []

        for cat in self._DUMMYJSON_CATS:
            try:
                url  = f"{self._DUMMYJSON_BASE}/products/category/{cat}"
                resp = self._session.get(  # type: ignore[union-attr]
                    url,
                    params={"limit": 100, "skip": 0},
                    timeout=10,
                )
                if resp.status_code != 200:
                    self.logger.debug(
                        "DummyJSON category '%s' returned HTTP %d", cat, resp.status_code
                    )
                    continue
                products = resp.json().get("products", [])
                for prod in products:
                    pid = prod.get("id")
                    if pid and pid not in seen_ids:
                        seen_ids.add(pid)
                        all_products.append(prod)
            except Exception as exc:
                self.logger.debug("DummyJSON category '%s' error: %s", cat, exc)

        return all_products

    def _fetch_via_search(self, unresolved_skus: List[str]) -> Dict[str, Dict]:
        """
        For SKUs not satisfied by the category sweep, issue one targeted
        DummyJSON search per SKU (using the first search keyword).
        Returns partial result dict for the resolved SKUs only.
        """
        result: Dict[str, Dict] = {}

        for sku_id in unresolved_skus:
            keywords = self._SKU_KEYWORDS.get(sku_id, [])
            if not keywords:
                continue
            # Try each keyword in order until a hit is found
            for kw in keywords:
                try:
                    resp = self._session.get(  # type: ignore[union-attr]
                        f"{self._DUMMYJSON_BASE}/products/search",
                        params={"q": kw, "limit": 10},
                        timeout=8,
                    )
                    if resp.status_code != 200:
                        continue
                    products = resp.json().get("products", [])
                    matched  = self._map_products_to_skus(products)
                    if sku_id in matched:
                        result[sku_id] = matched[sku_id]
                        self.logger.debug(
                            "DummyJSON search resolved '%s' via keyword '%s'", sku_id, kw
                        )
                        break
                except Exception as exc:
                    self.logger.debug(
                        "DummyJSON search error for '%s'/'%s': %s", sku_id, kw, exc
                    )

        return result

    # ── Private: SKU resolution & price localisation ─────────────────────────

    def _map_products_to_skus(self, products: List[Dict]) -> Dict[str, Dict]:
        """
        Score each DummyJSON product against every unresolved SKU's keyword
        list, select the highest-affinity match, convert the USD price to BDT,
        clamp within the configured band of the reference price, and return the
        resulting sku_id → record mapping.
        """
        result: Dict[str, Dict] = {}

        for sku_id, keywords in self._SKU_KEYWORDS.items():
            best_prod:  Optional[Dict] = None
            best_score: int            = 0

            for prod in products:
                title       = (prod.get("title", "") + " " + prod.get("description", "")).lower()
                category    = prod.get("category", "").lower()
                match_score = 0
                for kw in keywords:
                    if kw in title:
                        match_score += 2           # title hit is weighted higher
                    if kw in category:
                        match_score += 1
                if match_score > best_score:
                    best_score = match_score
                    best_prod  = prod

            if best_prod is None or best_score == 0:
                continue

            entry = self._build_sku_record(sku_id, best_prod)
            if entry is not None:
                result[sku_id] = entry

        return result

    def _build_sku_record(
        self, sku_id: str, prod: Dict
    ) -> Optional[Dict]:
        """
        Construct a normalised SKU record from a raw DummyJSON product dict.

        Price pipeline:
          USD price → BDT conversion → clamp within ±40 % of reference price
          → apply DummyJSON discount to simulate sale pricing
        """
        raw_usd = prod.get("price")
        if not isinstance(raw_usd, (int, float)) or raw_usd <= 0:
            return None

        ref_price = float(REFERENCE_PRICES.get(sku_id, {}).get("price", 0))
        if ref_price <= 0:
            return None

        # Convert & clamp
        bdt_price   = float(raw_usd) * self._USD_TO_BDT
        clamp_lo    = ref_price * (1.0 - self._PRICE_CLAMP_BAND)
        clamp_hi    = ref_price * (1.0 + self._PRICE_CLAMP_BAND)
        live_price  = max(clamp_lo, min(clamp_hi, bdt_price))

        # Apply DummyJSON discount percentage (0–100) as an additional markdown
        discount_pct = float(prod.get("discountPercentage", 0))
        discount_pct = max(0.0, min(discount_pct, 40.0))    # cap at 40 %
        discounted_price = round(live_price * (1.0 - discount_pct / 100.0), 2)

        # Normalise availability status
        raw_avail  = str(prod.get("availabilityStatus", "in stock")).lower().strip()
        stock_qty  = int(prod.get("stock", 50))
        if stock_qty <= 0:
            stock_label = "Out of Stock"
        elif stock_qty <= 10:
            stock_label = "Low Stock"
        else:
            stock_label = self._STOCK_STATUS_MAP.get(raw_avail, "In Stock")

        return {
            "price":      discounted_price,
            "prev_price": round(live_price, 2),   # pre-discount = "previous" price
            "stock":      stock_label,
            "source":     "live_api",
            "raw_name":   prod.get("title", ""),
            "rating":     float(prod.get("rating", 0)),
            "discount":   discount_pct,
        }

    # ── Private: Weather ──────────────────────────────────────────────────────

    def _call_wttr_api(self) -> Dict[str, Any]:
        """
        Fetch current Dhaka weather from wttr.in (JSON1 feed).
        Returns a fully-populated dict; falls back to sensible defaults on error.
        """
        default: Dict[str, Any] = {
            "temp_c":      30,
            "feels_like":  34,
            "humidity":    75,
            "condition":   "Partly Cloudy",
            "wind_kph":    12,
            "rain_chance": 20,
            "uv_index":    6,
            "source":      "default",
        }
        if not BS4_AVAILABLE:
            return default
        try:
            resp = requests.get(
                "https://wttr.in/Dhaka?format=j1",
                timeout=7,
                headers={"User-Agent": "Mozilla/5.0"},
            )
            if resp.status_code != 200:
                return default
            data = resp.json()
            cur  = data["current_condition"][0]
            rain = int(
                data.get("weather", [{}])[0]
                    .get("hourly", [{}])[0]
                    .get("chanceofrain", 20)
            )
            return {
                "temp_c":      int(cur.get("temp_C",        30)),
                "feels_like":  int(cur.get("FeelsLikeC",    34)),
                "humidity":    int(cur.get("humidity",       75)),
                "condition":   cur.get("weatherDesc", [{}])[0].get("value", "Clear"),
                "wind_kph":    int(cur.get("windspeedKmph", 12)),
                "rain_chance": rain,
                "uv_index":    int(cur.get("uvIndex",        6)),
                "source":      "live",
            }
        except Exception as exc:
            self.logger.warning("Weather API error: %s", exc)
            return default


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 3 ── COGNITIVE / AI ENGINE (SOPTOM ALGORITHM)
# ═══════════════════════════════════════════════════════════════════════════════
# ─────────────────────────────────────────────────────────────────────────────

class NexusDatabase:
    """
    SQLite WAL-mode persistence layer.

    Tables: inventory, orders, prices, ai_logs, carbon_ledger, dss_scores, alerts
    """

    SCHEMA = """
    CREATE TABLE IF NOT EXISTS inventory (
        sku_id          TEXT    PRIMARY KEY,
        name            TEXT    NOT NULL,
        category        TEXT,
        current_stock   INTEGER DEFAULT 0,
        reorder_point   INTEGER DEFAULT 20,
        eoq             INTEGER DEFAULT 50,
        unit_cost       REAL    DEFAULT 0,
        selling_price   REAL    DEFAULT 0,
        expiry_days     INTEGER DEFAULT 7,
        supplier        TEXT    DEFAULT 'Local Market',
        updated_at      TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS orders (
        order_id     INTEGER PRIMARY KEY AUTOINCREMENT,
        sku_id       TEXT    NOT NULL,
        quantity     INTEGER NOT NULL,
        unit_price   REAL    NOT NULL,
        customer_id  TEXT,
        zone         TEXT,
        rider_id     TEXT,
        status       TEXT    DEFAULT 'pending',
        created_at   TEXT    DEFAULT (datetime('now')),
        delivered_at TEXT
    );
    CREATE TABLE IF NOT EXISTS prices (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        sku_id      TEXT    NOT NULL,
        price       REAL    NOT NULL,
        prev_price  REAL,
        data_source TEXT    DEFAULT 'scraper',
        captured_at TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS ai_logs (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        event_type  TEXT,
        sku_id      TEXT,
        payload     TEXT,
        result      TEXT,
        model_used  TEXT,
        tokens_used INTEGER DEFAULT 0,
        created_at  TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS carbon_ledger (
        id               INTEGER PRIMARY KEY AUTOINCREMENT,
        route_id         TEXT,
        traditional_km   REAL,
        optimal_km       REAL,
        fuel_saved_l     REAL,
        co2_saved_kg     REAL,
        cost_saved_bdt   REAL,
        recorded_at      TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS dss_scores (
        id           INTEGER PRIMARY KEY AUTOINCREMENT,
        sku_id       TEXT,
        total_score  REAL,
        demand_score REAL,
        price_score  REAL,
        stock_score  REAL,
        expiry_score REAL,
        margin_score REAL,
        action       TEXT,
        scored_at    TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS alerts (
        id           INTEGER PRIMARY KEY AUTOINCREMENT,
        severity     TEXT    DEFAULT 'info',
        category     TEXT,
        message      TEXT,
        sku_id       TEXT,
        acknowledged INTEGER DEFAULT 0,
        created_at   TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS users (
        id              INTEGER PRIMARY KEY AUTOINCREMENT,
        username        TEXT    UNIQUE NOT NULL,
        email           TEXT    UNIQUE NOT NULL,
        name            TEXT    NOT NULL,
        hashed_password TEXT    NOT NULL,
        role            TEXT    NOT NULL DEFAULT 'dispatcher',
        is_active       INTEGER NOT NULL DEFAULT 1,
        created_at      TEXT    DEFAULT (datetime('now'))
    );
    CREATE TABLE IF NOT EXISTS audit_logs (
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        username    TEXT    NOT NULL,
        role        TEXT    NOT NULL,
        action_type TEXT    NOT NULL,
        description TEXT,
        ip_hint     TEXT    DEFAULT 'streamlit-session',
        timestamp   TEXT    DEFAULT (datetime('now'))
    );
    """

    def __init__(self, db_path: str = DB_PATH) -> None:
        self.db_path = db_path
        self.logger  = logging.getLogger(self.__class__.__name__)
        self._lock   = threading.Lock()                        # ← thread-safe write gate
        self._conn   = sqlite3.connect(db_path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._conn.execute("PRAGMA journal_mode=WAL;")
        self._conn.execute("PRAGMA foreign_keys=ON;")
        self._conn.execute("PRAGMA busy_timeout=5000;")        # wait up to 5 s on lock
        self._bootstrap_schema()
        self._seed_inventory()
        self._seed_orders()
        self._seed_default_users()                             # ← RBAC: seed users on first run

    # ── CRUD ──────────────────────────────────────────────────────────────────

    def execute_query(self, sql: str, params: tuple = (), commit: bool = True) -> Optional[sqlite3.Cursor]:
        with self._lock:                                       # ← serialise concurrent writes
            try:
                cur = self._conn.execute(sql, params)
                if commit:
                    self._conn.commit()
                return cur
            except sqlite3.Error as exc:
                self.logger.error("DB write: %s | sql: %.80s", exc, sql)
                try:
                    self._conn.rollback()
                except Exception:
                    pass
                return None

    def fetch_all(self, sql: str, params: tuple = ()) -> List[Dict]:
        with self._lock:                                       # ← serialise concurrent reads
            try:
                cur = self._conn.execute(sql, params)
                return [dict(r) for r in cur.fetchall()]
            except sqlite3.Error as exc:
                self.logger.error("DB read: %s", exc)
                return []

    def fetch_one(self, sql: str, params: tuple = ()) -> Optional[Dict]:
        rows = self.fetch_all(sql, params)
        return rows[0] if rows else None

    # ── Domain writes ─────────────────────────────────────────────────────────

    def upsert_price(self, sku_id: str, price: float, prev_price: float, source: str = "scraper") -> None:
        self.execute_query(
            "INSERT INTO prices (sku_id, price, prev_price, data_source) VALUES (?,?,?,?)",
            (sku_id, price, prev_price, source),
        )

    def log_ai_event(self, event_type: str, sku_id: str, payload: Dict, result: str, model: str, tokens: int = 0) -> None:
        self.execute_query(
            "INSERT INTO ai_logs (event_type,sku_id,payload,result,model_used,tokens_used) VALUES (?,?,?,?,?,?)",
            (event_type, sku_id, json.dumps(payload), result, model, tokens),
        )

    def log_dss_score(self, sku_id: str, scores: Dict, action: str) -> None:
        self.execute_query(
            "INSERT INTO dss_scores (sku_id,total_score,demand_score,price_score,"
            "stock_score,expiry_score,margin_score,action) VALUES (?,?,?,?,?,?,?,?)",
            (sku_id, scores.get("total_score", 0), scores.get("demand_score", 0),
             scores.get("price_score", 0), scores.get("stock_score", 0),
             scores.get("expiry_score", 0), scores.get("margin_score", 0), action),
        )

    def add_alert(self, severity: str, category: str, message: str, sku_id: str = "") -> None:
        existing = self.fetch_one(
            "SELECT id FROM alerts WHERE message=? AND created_at > datetime('now','-30 minutes')",
            (message,),
        )
        if not existing:
            self.execute_query(
                "INSERT INTO alerts (severity,category,message,sku_id) VALUES (?,?,?,?)",
                (severity, category, message, sku_id),
            )

    def log_carbon(self, route_id: str, traditional_km: float, optimal_km: float,
                   fuel_saved: float, co2_saved: float, cost_saved: float) -> None:
        self.execute_query(
            "INSERT INTO carbon_ledger (route_id,traditional_km,optimal_km,"
            "fuel_saved_l,co2_saved_kg,cost_saved_bdt) VALUES (?,?,?,?,?,?)",
            (route_id, traditional_km, optimal_km, fuel_saved, co2_saved, cost_saved),
        )

    def update_inventory_from_prices(self, prices: Dict[str, Dict]) -> None:
        """
        Sync live scraped retail prices into the inventory and price-history tables.

        IMPORTANT — unit_cost separation:
        ──────────────────────────────────
        ``unit_cost`` represents the *procurement / landed cost* seeded at startup
        and should only be changed when a purchase order is placed.  It must NEVER
        be overwritten by the live retail (Chaldal) price; doing so collapses Gross
        Margin to zero because both numerator and denominator become the same value.

        The scraped retail price is stored in two places:
          1. ``inventory.selling_price``  — fast lookup for GM calculation.
          2. ``prices`` table             — full time-series / audit trail.
        """
        for sku_id, info in prices.items():
            price      = info.get("price", 0)
            prev_price = info.get("prev_price", price)
            src        = info.get("data_source", "scraper")
            if price > 0:
                # Update ONLY the selling_price column; unit_cost stays static.
                self.execute_query(
                    "UPDATE inventory SET selling_price=?, updated_at=datetime('now') WHERE sku_id=?",
                    (price, sku_id),
                )
                self.upsert_price(sku_id, price, prev_price, src)

    def place_order(self, sku_id: str, quantity: int, unit_price: float,
                    customer_id: str, zone: str) -> Optional[int]:
        cur = self.execute_query(
            "INSERT INTO orders (sku_id,quantity,unit_price,customer_id,zone) VALUES (?,?,?,?,?)",
            (sku_id, quantity, unit_price, customer_id, zone),
        )
        return cur.lastrowid if cur else None

    def acknowledge_alert(self, alert_id: int) -> None:
        self.execute_query("UPDATE alerts SET acknowledged=1 WHERE id=?", (alert_id,))

    def acknowledge_all_alerts(self) -> None:
        self.execute_query("UPDATE alerts SET acknowledged=1 WHERE acknowledged=0")

    # ── RBAC — User management ─────────────────────────────────────────────────

    @staticmethod
    def hash_password(plain: str) -> str:
        """
        Hash a plaintext password.
        Uses bcrypt (pip install bcrypt) when available; falls back to
        PBKDF2-HMAC-SHA256 (stdlib) so the app always works without bcrypt.
        """
        if BCRYPT_AVAILABLE:
            return _bcrypt.hashpw(plain.encode("utf-8"), _bcrypt.gensalt(rounds=12)).decode("utf-8")
        # PBKDF2-HMAC-SHA256 fallback: salt$iterations$hash (all hex)
        salt = secrets.token_hex(16)
        iterations = 260_000
        dk = hashlib.pbkdf2_hmac("sha256", plain.encode("utf-8"), salt.encode(), iterations)
        return f"pbkdf2${salt}${iterations}${dk.hex()}"

    @staticmethod
    def verify_password(plain: str, hashed: str) -> bool:
        """Verify a plaintext password against a stored hash (bcrypt or PBKDF2)."""
        try:
            if hashed.startswith("$2"):          # bcrypt hash
                if not BCRYPT_AVAILABLE:
                    return False
                return _bcrypt.checkpw(plain.encode("utf-8"), hashed.encode("utf-8"))
            if hashed.startswith("pbkdf2$"):     # PBKDF2 fallback
                _, salt, iterations_s, stored_hex = hashed.split("$")
                iterations = int(iterations_s)
                dk = hashlib.pbkdf2_hmac("sha256", plain.encode("utf-8"),
                                          salt.encode(), iterations)
                return hmac.compare_digest(dk.hex(), stored_hex)
        except Exception:
            pass
        return False

    def get_user(self, username: str) -> Optional[Dict]:
        """Fetch a single active user row by username."""
        return self.fetch_one(
            "SELECT * FROM users WHERE username=? AND is_active=1", (username,)
        )

    def create_user(self, username: str, email: str, name: str,
                    plain_password: str, role: str) -> bool:
        """
        Create a new user with a hashed password.
        Returns True on success, False if username/email already exists.
        """
        hashed = self.hash_password(plain_password)
        cur = self.execute_query(
            "INSERT OR IGNORE INTO users (username,email,name,hashed_password,role) "
            "VALUES (?,?,?,?,?)",
            (username, email, name, hashed, role),
        )
        return bool(cur and cur.rowcount)

    def change_password(self, username: str, new_plain: str) -> bool:
        """Update a user's password hash."""
        hashed = self.hash_password(new_plain)
        cur = self.execute_query(
            "UPDATE users SET hashed_password=? WHERE username=?",
            (hashed, username),
        )
        return bool(cur and cur.rowcount)

    def list_users(self) -> List[Dict]:
        """Return all users (hashed_password omitted for security)."""
        return self.fetch_all(
            "SELECT id,username,email,name,role,is_active,created_at FROM users ORDER BY id"
        )

    def deactivate_user(self, username: str) -> None:
        self.execute_query("UPDATE users SET is_active=0 WHERE username=?", (username,))

    # ── RBAC — Audit logging ───────────────────────────────────────────────────

    def log_audit(self, username: str, role: str,
                  action_type: str, description: str) -> None:
        """
        Write a row to the audit_logs table.
        Prefer calling the NexusUI helper `log_action()` which auto-fills
        username/role from st.session_state.
        """
        self.execute_query(
            "INSERT INTO audit_logs (username,role,action_type,description) "
            "VALUES (?,?,?,?)",
            (username, role, action_type, description),
        )

    def get_audit_logs(self, limit: int = 50) -> List[Dict]:
        return self.fetch_all(
            "SELECT username,role,action_type,description,timestamp "
            "FROM audit_logs ORDER BY timestamp DESC LIMIT ?", (limit,)
        )

    # ── Private: seed default users ───────────────────────────────────────────

    def _seed_default_users(self) -> None:
        """
        Create three built-in accounts on first run.
        Passwords are hashed at seed time — never stored in plaintext.

        Default credentials (CHANGE IN PRODUCTION):
          admin      / Admin@1234   → role: admin
          manager    / Manager@456  → role: manager
          dispatcher / Rider@789    → role: dispatcher
        """
        n = (self.fetch_one("SELECT COUNT(*) as n FROM users") or {}).get("n", 0)
        if n > 0:
            return   # already seeded — skip silently

        defaults = [
            ("admin",      "admin@logix.bd",      "Sourab Dey Soptom", "Admin@1234",   "admin"),
            ("manager",    "manager@logix.bd",     "Karim Manager",     "Manager@456",  "manager"),
            ("dispatcher", "dispatcher@logix.bd",  "Rahim Rider",       "Rider@789",    "dispatcher"),
        ]
        for username, email, name, plain_pw, role in defaults:
            self.create_user(username, email, name, plain_pw, role)
        self.logger.info("RBAC: seeded 3 default users (admin / manager / dispatcher)")

    # ── Domain reads ──────────────────────────────────────────────────────────

    def get_inventory(self) -> List[Dict]:
        return self.fetch_all("SELECT * FROM inventory ORDER BY category, name")

    def get_recent_orders(self, limit: int = 30) -> List[Dict]:
        return self.fetch_all(
            "SELECT * FROM orders ORDER BY created_at DESC LIMIT ?", (limit,)
        )

    def get_carbon_total(self) -> Dict:
        row = self.fetch_one(
            "SELECT SUM(fuel_saved_l) as fuel, SUM(co2_saved_kg) as co2, "
            "SUM(cost_saved_bdt) as cost, COUNT(*) as routes FROM carbon_ledger"
        )
        return row or {"fuel": 0, "co2": 0, "cost": 0, "routes": 0}

    def get_price_history(self, sku_id: str, limit: int = 30) -> List[Dict]:
        return self.fetch_all(
            "SELECT price, prev_price, data_source, captured_at FROM prices "
            "WHERE sku_id=? ORDER BY captured_at DESC LIMIT ?",
            (sku_id, limit),
        )

    def get_unacknowledged_alerts(self) -> List[Dict]:
        return self.fetch_all(
            "SELECT * FROM alerts WHERE acknowledged=0 ORDER BY created_at DESC LIMIT 50"
        )

    def get_alert_count(self) -> Dict[str, int]:
        rows = self.fetch_all(
            "SELECT severity, COUNT(*) as n FROM alerts WHERE acknowledged=0 GROUP BY severity"
        )
        return {r["severity"]: r["n"] for r in rows}

    def get_dss_history(self, limit: int = 50) -> List[Dict]:
        return self.fetch_all(
            "SELECT sku_id, total_score, action, scored_at FROM dss_scores "
            "ORDER BY scored_at DESC LIMIT ?", (limit,)
        )

    def get_ai_logs(self, limit: int = 15) -> List[Dict]:
        return self.fetch_all(
            "SELECT event_type, sku_id, model_used, tokens_used, created_at "
            "FROM ai_logs ORDER BY created_at DESC LIMIT ?", (limit,)
        )

    def get_order_stats(self) -> Dict:
        row = self.fetch_one(
            "SELECT COUNT(*) as total, "
            "SUM(CASE WHEN status='delivered'  THEN 1 ELSE 0 END) as delivered, "
            "SUM(CASE WHEN status='pending'    THEN 1 ELSE 0 END) as pending, "
            "SUM(CASE WHEN status='in_transit' THEN 1 ELSE 0 END) as in_transit, "
            "SUM(CASE WHEN status='processing' THEN 1 ELSE 0 END) as processing, "
            "SUM(quantity * unit_price) as revenue "
            "FROM orders"
        )
        return row or {}

    def get_daily_revenue(self, days: int = 7) -> List[Dict]:
        return self.fetch_all(
            "SELECT date(created_at) as day, "
            "SUM(quantity * unit_price) as revenue, "
            "COUNT(*) as order_count "
            "FROM orders "
            "WHERE created_at >= datetime('now', ? || ' days') "
            "GROUP BY date(created_at) "
            "ORDER BY day ASC",
            (f"-{days}",),
        )

    def get_zone_stats(self) -> List[Dict]:
        return self.fetch_all(
            "SELECT zone, COUNT(*) as orders, SUM(quantity*unit_price) as revenue "
            "FROM orders GROUP BY zone ORDER BY orders DESC"
        )

    # ── Private helpers ───────────────────────────────────────────────────────

    def _bootstrap_schema(self) -> None:
        stmts = [s.strip() for s in self.SCHEMA.strip().split(";") if s.strip()]
        for stmt in stmts:
            try:
                self._conn.execute(stmt)
            except sqlite3.Error as exc:
                self.logger.error("Schema error: %s", exc)
        # ── Live migration: add selling_price column to existing databases ──────
        try:
            self._conn.execute("ALTER TABLE inventory ADD COLUMN selling_price REAL DEFAULT 0")
            self.logger.info("Migration: added selling_price column to inventory table")
        except sqlite3.OperationalError:
            pass   # column already exists — normal on fresh or already-migrated DBs
        self._conn.commit()

    def _seed_inventory(self) -> None:
        n = (self.fetch_one("SELECT COUNT(*) as n FROM inventory") or {}).get("n", 0)
        if n > 0:
            return
        rows = [
            ("onion_kg",   "Onion",              "Vegetables", 120, 30,  80,  70,  70,  5,  "Karwan Bazar"),
            ("potato_kg",  "Potato",             "Vegetables", 200, 40, 100,  50,  50, 14,  "Karwan Bazar"),
            ("rice_5kg",   "Rice (5 kg)",        "Staples",     80, 20,  50, 345, 345,180,  "Narayanganj"),
            ("chicken_kg", "Chicken",            "Meat",        45, 15,  40, 235, 235,  2,  "Gabtoli Market"),
            ("egg_12",     "Eggs (12 pcs)",      "Protein",    150, 25,  70, 150, 150, 21,  "Savar Farm"),
            ("tomato_kg",  "Tomato",             "Vegetables",  60, 20,  55,  85,  85,  3,  "Jatrabari"),
            ("lentil_kg",  "Red Lentil",         "Staples",    180, 40,  90, 135, 135, 90,  "Chwak Bazar"),
            ("oil_1l",     "Soybean Oil 1 L",    "Cooking",    200, 50, 110, 175, 175,365,  "Distributor"),
            ("flour_kg",   "Flour (Atta 1 kg)",  "Staples",    160, 35,  80,  58,  58,180,  "Distributor"),
            ("sugar_kg",   "Sugar",              "Staples",    140, 30,  75, 130, 130,180,  "Distributor"),
        ]
        for row in rows:
            self.execute_query(
                "INSERT OR IGNORE INTO inventory "
                "(sku_id,name,category,current_stock,reorder_point,eoq,unit_cost,selling_price,expiry_days,supplier) "
                "VALUES (?,?,?,?,?,?,?,?,?,?)",
                row,
            )

    def _seed_orders(self) -> None:
        n = (self.fetch_one("SELECT COUNT(*) as n FROM orders") or {}).get("n", 0)
        if n > 0:
            return
        zones    = list(DHAKA_HUBS.keys())
        statuses = ["pending","pending","processing","in_transit","delivered","delivered","delivered"]
        base_pr  = {s: REFERENCE_PRICES[s]["price"] for s in SKUS}
        for i in range(60):
            sku    = list(SKUS.keys())[i % len(SKUS)]
            qty    = (i % 4) + 1
            price  = base_pr[sku] * random.uniform(0.95, 1.08)
            zone   = zones[i % len(zones)]
            status = statuses[i % len(statuses)]
            self.execute_query(
                "INSERT OR IGNORE INTO orders "
                "(sku_id,quantity,unit_price,customer_id,zone,status) "
                "VALUES (?,?,?,?,?,?)",
                (sku, qty, round(price, 2), f"CUST{i+1:03d}", zone, status),
            )


class SoptomAlgorithm:
    """
    SOPTOM — Supply Optimisation & Predictive Trend Operations Module.

    AI Client Priority:
    1. Grok xAI (api.x.ai) via openai-compatible SDK
    2. Groq SDK fallback
    3. Rule-based engine (always available, zero latency)

    LLM Reliability Contract:
    ─────────────────────────
    Every public method that calls the LLM wraps _call_llm() inside a
    _safe_llm_call() guard that catches network errors, rate-limit (HTTP 429),
    timeout, and unexpected SDK exceptions — then degrades gracefully to the
    corresponding rule-based method without raising or crashing Streamlit.
    """

    LOOKBACK      = 14
    LSTM_UNITS    = 64
    EPOCHS        = 8
    BATCH_SIZE    = 8

    # Retry / timeout configuration
    _LLM_TIMEOUT_SEC   = 18     # hard wall-clock timeout per API call
    _LLM_MAX_RETRIES   = 1      # one silent retry on transient error, then fallback
    _LLM_RETRY_DELAY   = 1.5   # seconds to wait before retry

    # System-level instruction injected into every LLM call
    _SYSTEM_INSTRUCTION = (
        "You are SOPTOM, the AI supply-chain intelligence engine embedded inside "
        "LOGIX — a production-grade supply chain platform developed by Sourab Dey Soptom.\n\n"
        "STRICT OPERATING RULES — VIOLATING ANY RULE VOIDS YOUR RESPONSE:\n"
        "1. BASE EVERY CLAIM EXCLUSIVELY on the structured data provided in the prompt. "
        "   Do NOT invent, extrapolate, or assume any number, price, quantity, or fact "
        "   that is not explicitly present in the input data.\n"
        "2. NEVER fabricate prices, percentages, order quantities, or dates. "
        "   If a value is missing from the data, state 'data unavailable' for that item.\n"
        "3. Be CONCISE and ANALYTICAL. Eliminate all filler, pleasantries, and preamble. "
        "   Every sentence must deliver a distinct, actionable or factual insight.\n"
        "4. Quantify recommendations using only numbers derived from the supplied data. "
        "   Show your arithmetic (e.g., 'stock 45 / EOQ 80 = 56% — order 35 units').\n"
        "5. Use Bangladeshi market context (BDT, Dhaka geography, local festivals) "
        "   only where it is directly supported by the event or data provided.\n"
        "6. OUTPUT FORMAT: plain text only. No markdown headers, no bullet symbols "
        "   beyond what the prompt explicitly requests."
    )

    # ── Class-level LSTM background-training cache ────────────────────────────
    # Shared across all instances / reruns so trained weights survive Streamlit
    # page refreshes without retraining from scratch.
    _lstm_bg_cache:    Dict[str, Dict]  = {}   # sku_id → completed forecast result
    _lstm_bg_training: Dict[str, bool]  = {}   # sku_id → True while thread is running
    _lstm_bg_lock:     threading.Lock   = threading.Lock()

    def __init__(self, db: Optional["NexusDatabase"] = None) -> None:
        self.logger      = logging.getLogger(self.__class__.__name__)
        self._db         = db                  # ← real orders DB for history queries
        self._client     = None
        self._model_name = "rule-based"
        self._models:    Dict[str, Any] = {}
        self._call_count = 0
        self._last_call_ts: float = 0.0
        self._init_llm_client()

    # ── LLM client initialisation ─────────────────────────────────────────────

    def _init_llm_client(self) -> None:
        """
        Attempt to initialise the best available LLM client.
        Falls back silently to rule-based mode on any configuration error.
        """
        # Priority 1 — Grok xAI via OpenAI-compatible SDK
        if OPENAI_SDK and GROK_API_KEY:
            try:
                client = _OpenAI(api_key=GROK_API_KEY, base_url=GROK_BASE_URL)
                client.models.list()          # lightweight connectivity probe
                self._client     = client
                self._model_name = GROK_MODEL
                self.logger.info("Grok xAI client ready (model: %s)", GROK_MODEL)
                return
            except Exception as exc:
                self.logger.warning("Grok xAI initialisation failed: %s", exc)
                self._client = None

        # Priority 2 — Groq SDK fallback
        if GROQ_SDK:
            groq_key = os.getenv("GROQ_API_KEY", "")
            if groq_key:
                try:
                    client = _Groq(api_key=groq_key)
                    self._client     = client
                    self._model_name = GROQ_MODEL
                    self.logger.info("Groq fallback client ready (model: %s)", GROQ_MODEL)
                    return
                except Exception as exc:
                    self.logger.warning("Groq fallback initialisation failed: %s", exc)
                    self._client = None
            else:
                self.logger.info("Groq SDK available but GROQ_API_KEY not set; using rule-based engine.")

        self.logger.info("SOPTOM running in rule-based mode (no LLM client available).")

    # ── Public API ────────────────────────────────────────────────────────────

    def forecast_demand(
        self,
        sku_id: str,
        historical_data: Optional[List[float]] = None,
        event: str = "Normal Day",
    ) -> Dict:
        # ── 1. Resolve history: caller-supplied > real DB > flat baseline ──────
        if historical_data and len(historical_data) >= self.LOOKBACK:
            history = historical_data
        else:
            history = self.fetch_sales_history_from_db(sku_id)

        factor = EVENT_DEMAND_FACTORS.get(event, {}).get(sku_id, 1.0)

        if _try_import_tf() and NP_AVAILABLE:
            try:
                result = self._lstm_forecast(sku_id, history)
                result["forecast"]     = [round(v * factor, 1) for v in result["forecast"]]
                result["event_factor"] = factor
                return result
            except Exception as exc:
                self.logger.info("LSTM for '%s': %s — using Holt's this cycle", sku_id, exc)

        result = self._holts_forecast(sku_id, history)
        result["forecast"]     = [round(v * factor, 1) for v in result["forecast"]]
        result["event_factor"] = factor
        return result

    def analyze_market_context(
        self, event: str, live_prices: Dict, weather: Dict
    ) -> str:
        if self._client:
            result = self._safe_llm_call(
                prompt      = self._build_market_prompt(event, live_prices, weather),
                max_tokens  = 380,
                call_label  = "market_context",
                fallback_fn = lambda: self._rule_based_market_analysis(event, live_prices, weather),
            )
            return result
        return self._rule_based_market_analysis(event, live_prices, weather)

    def analyze_sku_deep(
        self, sku_id: str, sku_data: Dict, forecast: Dict, weather: Dict
    ) -> str:
        if self._client:
            result = self._safe_llm_call(
                prompt      = self._build_sku_prompt(sku_id, sku_data, forecast, weather),
                max_tokens  = 380,
                call_label  = f"sku_deep:{sku_id}",
                fallback_fn = lambda: self._rule_based_sku_analysis(sku_id, sku_data, forecast),
            )
            return result
        return self._rule_based_sku_analysis(sku_id, sku_data, forecast)

    def generate_procurement_plan(
        self,
        inventory: List[Dict],
        forecasts: Dict[str, Dict],
        event: str,
    ) -> str:
        low_stock = [
            i for i in inventory
            if i.get("current_stock", 999) < i.get("reorder_point", 20) * 1.3
        ]
        fcast_summary = {
            k: {
                "avg_7d_demand": round(
                    sum(v.get("forecast", [0])) / max(len(v.get("forecast", [1])), 1), 1
                ),
                "peak_demand": max(v.get("forecast", [0])),
                "peak_day":    v.get("peak_day", 1),
                "method":      v.get("method", "unknown"),
            }
            for k, v in forecasts.items()
        }

        if self._client:
            prompt = self._build_procurement_prompt(low_stock, fcast_summary, event)
            return self._safe_llm_call(
                prompt      = prompt,
                max_tokens  = 550,
                call_label  = "procurement_plan",
                fallback_fn = lambda: self._fallback_procurement(low_stock, event),
            )
        return self._fallback_procurement(low_stock, event)

    def is_llm_active(self) -> bool:
        return self._client is not None

    def get_model_name(self) -> str:
        return self._model_name if self._client else "Rule-based engine"

    # ── Private: Resilient LLM gateway ───────────────────────────────────────

    def _safe_llm_call(
        self,
        prompt: str,
        max_tokens: int,
        call_label: str,
        fallback_fn: Any,
    ) -> str:
        """
        Execute an LLM call with:
          • A hard timeout enforced via a retry-and-sleep loop
          • Automatic retry (up to _LLM_MAX_RETRIES) on transient errors
          • Graceful degradation to fallback_fn on rate-limit (HTTP 429),
            timeout, connection error, or any unexpected SDK exception
          • Minimum inter-call spacing to avoid self-induced rate limiting

        Returns the LLM response string, or the result of fallback_fn().
        """
        # Enforce a minimum gap between consecutive API calls (100 ms)
        gap = time.time() - self._last_call_ts
        if gap < 0.1:
            time.sleep(0.1 - gap)

        last_exc: Optional[Exception] = None
        attempts = self._LLM_MAX_RETRIES + 1

        for attempt in range(1, attempts + 1):
            try:
                response = self._call_llm(prompt, max_tokens)
                self._call_count   += 1
                self._last_call_ts  = time.time()
                return response

            except Exception as exc:
                last_exc    = exc
                exc_text    = str(exc).lower()
                exc_type    = type(exc).__name__

                # Detect rate limiting — no point retrying immediately
                is_rate_limit = (
                    "429" in exc_text
                    or "rate limit" in exc_text
                    or "rate_limit" in exc_text
                    or "too many requests" in exc_text
                    or "quota" in exc_text
                )
                # Detect hard auth / config errors — no point retrying at all
                is_fatal = (
                    "401" in exc_text
                    or "403" in exc_text
                    or "invalid api key" in exc_text
                    or "authentication" in exc_text
                )

                if is_fatal:
                    self.logger.error(
                        "[%s] LLM fatal auth error on attempt %d/%d (%s: %s) — "
                        "disabling LLM client and switching to rule-based.",
                        call_label, attempt, attempts, exc_type, exc,
                    )
                    self._client = None       # prevent further calls this session
                    break

                if is_rate_limit:
                    self.logger.warning(
                        "[%s] LLM rate-limit on attempt %d/%d — backing off %.1fs.",
                        call_label, attempt, attempts, self._LLM_RETRY_DELAY * attempt,
                    )
                    time.sleep(self._LLM_RETRY_DELAY * attempt)
                    # Only retry once on rate-limit
                    if attempt >= 2:
                        break
                    continue

                # Transient network / timeout / SDK error
                if attempt < attempts:
                    self.logger.warning(
                        "[%s] LLM transient error attempt %d/%d (%s: %s) — retrying in %.1fs.",
                        call_label, attempt, attempts, exc_type, exc, self._LLM_RETRY_DELAY,
                    )
                    time.sleep(self._LLM_RETRY_DELAY)
                else:
                    self.logger.warning(
                        "[%s] LLM failed after %d attempt(s) (%s: %s) — using rule-based fallback.",
                        call_label, attempts, exc_type, exc,
                    )

        # All retries exhausted or fatal error — invoke rule-based fallback
        try:
            return fallback_fn()
        except Exception as fb_exc:
            self.logger.error(
                "[%s] Rule-based fallback also failed: %s", call_label, fb_exc
            )
            return "Analysis temporarily unavailable. Please refresh or try again."

    def _call_llm(self, prompt: str, max_tokens: int = 300) -> str:
        """
        Raw LLM invocation.  Always uses a system message to enforce grounding
        and injects a low temperature to minimise hallucination.
        Both OpenAI-SDK (Grok) and Groq SDK share the same chat.completions API.
        """
        messages = [
            {"role": "system", "content": self._SYSTEM_INSTRUCTION},
            {"role": "user",   "content": prompt},
        ]
        resp = self._client.chat.completions.create(  # type: ignore[union-attr]
            model       = self._model_name,
            messages    = messages,
            max_tokens  = max_tokens,
            temperature = 0.20,     # low temp → factual, grounded, reproducible
            top_p       = 0.85,
        )
        content = resp.choices[0].message.content
        if not content or not content.strip():
            raise ValueError("LLM returned an empty response body.")
        return content.strip()

    # ── Private: Prompt builders ──────────────────────────────────────────────

    def _build_market_prompt(
        self, event: str, live_prices: Dict, weather: Dict
    ) -> str:
        """
        Construct a tightly-scoped market-context prompt.
        All numbers are sourced directly from live_prices and weather;
        the model is explicitly forbidden from inventing additional figures.
        """
        # Build a structured price table with delta direction and magnitude
        price_rows: List[str] = []
        for sid, info in live_prices.items():
            cur  = info.get("price", 0)
            prev = info.get("prev_price", cur)
            if cur and prev and prev > 0:
                delta_pct = ((cur - prev) / prev) * 100
                arrow     = "▲" if delta_pct > 0 else ("▼" if delta_pct < 0 else "→")
                delta_str = f"{arrow}{abs(delta_pct):.1f}%"
            else:
                delta_str = "→ n/a"
            price_rows.append(
                f"  {info.get('name', sid):<22} ৳{cur:<8.2f} {delta_str:<10} "
                f"stock={info.get('stock','?'):<12} src={info.get('data_source','?')}"
            )

        # Event demand factors for this specific event (data-driven, not invented)
        event_factors = EVENT_DEMAND_FACTORS.get(event, {})
        high_impact   = [
            f"{SKUS[s][0]} (×{f:.2f})"
            for s, f in sorted(event_factors.items(), key=lambda x: -x[1])
            if f != 1.0
        ]
        event_impact_str = ", ".join(high_impact[:6]) if high_impact else "No differential factors for this event."

        return (
            "═══ MARKET CONTEXT ANALYSIS REQUEST ═══\n\n"
            f"MARKET EVENT  : {event}\n\n"
            "LIVE PRICE TABLE (sourced from DummyJSON → BDT-converted; do NOT invent prices):\n"
            f"{'SKU':<22} {'Price (৳)':<10} {'Δ vs Prev':<10} {'Stock':<14} Source\n"
            f"{'─'*70}\n"
            + "\n".join(price_rows)
            + f"\n\nEVENT DEMAND MULTIPLIERS (from system config — use these exact figures):\n"
            f"  {event_impact_str}\n\n"
            "CURRENT DHAKA WEATHER (live wttr.in feed):\n"
            f"  Temp      : {weather.get('temp_c', 'n/a')}°C  "
            f"(feels {weather.get('feels_like', 'n/a')}°C)\n"
            f"  Humidity  : {weather.get('humidity', 'n/a')}%\n"
            f"  Condition : {weather.get('condition', 'n/a')}\n"
            f"  Rain prob : {weather.get('rain_chance', 'n/a')}%\n"
            f"  Wind      : {weather.get('wind_kph', 'n/a')} km/h\n"
            f"  UV index  : {weather.get('uv_index', 'n/a')}\n\n"
            "═══ RESPONSE REQUIREMENTS ═══\n"
            "Produce exactly 4 sentences (no more, no less). Each sentence must:\n"
            "  [S1] Identify the top 2 SKUs most impacted by TODAY'S weather, "
            "citing the exact rain probability or temperature value from the data above.\n"
            "  [S2] Name any SKU whose price delta exceeds ±5% (use the Δ column above); "
            "if none, state 'No price anomalies detected.'\n"
            "  [S3] State ONE procurement action: specify the SKU name, a quantity derived "
            "from the event multiplier above, and the reason in ≤15 words.\n"
            "  [S4] State the delivery/logistics implication of the current weather + event "
            "in ≤20 words, referencing the rain probability or wind speed from the data.\n\n"
            "HARD CONSTRAINT: Every number you write must appear in the data above. "
            "If a number is not in the data, do not write it."
        )

    def _build_sku_prompt(
        self, sku_id: str, sku_data: Dict, forecast: Dict, weather: Dict
    ) -> str:
        """
        Build a single-SKU deep-analysis prompt.
        Provides a complete data snapshot and constrains output to 3 specific sentences.
        """
        fcast_list  = forecast.get("forecast", [])
        fcast_str   = ", ".join(f"৳{v:.1f}" if isinstance(v, float) else str(v) for v in fcast_list)
        peak_demand = max(fcast_list) if fcast_list else 0
        avg_demand  = round(sum(fcast_list) / max(len(fcast_list), 1), 1)
        cur_stock   = sku_data.get("current_stock", 0)
        eoq         = max(sku_data.get("eoq", 1), 1)
        reorder_pt  = sku_data.get("reorder_point", 20)
        expiry_days = sku_data.get("expiry_days", 999)
        price       = sku_data.get("price", 0)
        prev_price  = sku_data.get("prev_price", price)
        unit_cost   = sku_data.get("unit_cost", price)
        margin_pct  = round((price - unit_cost) / max(price, 1) * 100, 1) if price > 0 else 0

        # Pre-compute key ratios so the model never has to derive them
        stock_cover_days = round(cur_stock / max(avg_demand, 0.1), 1)
        gap_to_reorder   = cur_stock - reorder_pt
        order_urgency    = "CRITICAL" if cur_stock < reorder_pt else (
                           "ELEVATED" if cur_stock < reorder_pt * 1.3 else "NORMAL")
        price_delta_pct  = round(((price - prev_price) / max(prev_price, 1)) * 100, 2) if prev_price else 0

        return (
            "═══ SKU DEEP-ANALYSIS REQUEST ═══\n\n"
            f"SKU ID        : {sku_id}\n"
            f"Product       : {sku_data.get('name', sku_id)}  [{sku_data.get('category', 'N/A')}]\n"
            f"Supplier      : {sku_data.get('supplier', 'N/A')}\n\n"
            "── PRICING (do NOT invent prices outside this block) ──\n"
            f"  Current price : ৳{price:.2f}\n"
            f"  Previous price: ৳{prev_price:.2f}  (Δ {price_delta_pct:+.2f}%)\n"
            f"  Unit cost     : ৳{unit_cost:.2f}\n"
            f"  Gross margin  : {margin_pct:.1f}%\n"
            f"  Data source   : {sku_data.get('data_source', 'N/A')}\n\n"
            "── INVENTORY (pre-computed ratios — use these exact values) ──\n"
            f"  Current stock : {cur_stock} units\n"
            f"  Reorder point : {reorder_pt} units  (gap: {gap_to_reorder:+d} units)\n"
            f"  EOQ           : {eoq} units\n"
            f"  Order urgency : {order_urgency}\n"
            f"  Expiry window : {expiry_days} days\n"
            f"  Days of cover : {stock_cover_days} days (at avg demand {avg_demand} units/day)\n\n"
            "── 7-DAY DEMAND FORECAST (do NOT modify these values) ──\n"
            f"  Daily forecast: [{fcast_str}]\n"
            f"  Average       : {avg_demand} units/day\n"
            f"  Peak day      : Day {forecast.get('peak_day', '?')} "
            f"({peak_demand:.1f} units)\n"
            f"  Method        : {forecast.get('method', 'unknown')}  "
            f"[confidence: {forecast.get('confidence', 0):.0%}]\n"
            f"  Event factor  : ×{forecast.get('event_factor', 1.0):.2f}\n\n"
            "── WEATHER ──\n"
            f"  {weather.get('temp_c', 'n/a')}°C, "
            f"rain {weather.get('rain_chance', 'n/a')}%, "
            f"humidity {weather.get('humidity', 'n/a')}%\n\n"
            "═══ RESPONSE REQUIREMENTS ═══\n"
            "Write exactly 3 sentences. Derive every number from the data above.\n"
            "  [S1] INVENTORY ACTION: state the exact units to order (or hold/discount), "
            "calculated as: EOQ minus current stock = reorder quantity. "
            "Reference the order urgency flag and days of cover.\n"
            "  [S2] PRICING STRATEGY: recommend a specific price adjustment (in %) "
            "based on the margin and price delta. Quote the current margin.\n"
            "  [S3] TOP RISK FLAG: state the single most critical risk "
            "(stockout / expiry / margin compression / price spike) with the supporting number. "
            "Do not introduce any risk category not derivable from the data.\n\n"
            "HARD CONSTRAINT: do not write any number that does not appear in the data block above."
        )

    def _build_procurement_prompt(
        self,
        low_stock: List[Dict],
        fcast_summary: Dict[str, Dict],
        event: str,
    ) -> str:
        """
        Procurement plan prompt built from pre-aggregated data.
        Low-stock records are trimmed to the 6 most urgent items,
        and only the fields needed for decision-making are exposed.
        """
        # Slim the low-stock records to prevent prompt bloat
        trimmed = [
            {
                "sku_id":        i.get("sku_id", ""),
                "name":          i.get("name", ""),
                "current_stock": i.get("current_stock", 0),
                "reorder_point": i.get("reorder_point", 20),
                "eoq":           i.get("eoq", 50),
                "unit_cost_bdt": i.get("unit_cost", 0),
                "expiry_days":   i.get("expiry_days", 999),
                "supplier":      i.get("supplier", "TBD"),
                "urgency_ratio": round(
                    i.get("current_stock", 0) / max(i.get("reorder_point", 1), 1), 3
                ),
            }
            for i in sorted(
                low_stock[:6],
                key=lambda x: x.get("current_stock", 999) / max(x.get("reorder_point", 1), 1),
            )
        ]

        low_stock_json  = json.dumps(trimmed,        indent=2)
        fcast_json      = json.dumps(fcast_summary,  indent=2)
        event_factors   = EVENT_DEMAND_FACTORS.get(event, {})
        event_json      = json.dumps(
            {k: v for k, v in event_factors.items() if v != 1.0}, indent=2
        )

        return (
            "═══ 7-DAY PROCUREMENT PLAN REQUEST ═══\n\n"
            f"MARKET EVENT  : {event}\n\n"
            "CRITICAL / LOW-STOCK SKUs (sorted by urgency_ratio ASC — most urgent first):\n"
            f"{low_stock_json}\n\n"
            "7-DAY DEMAND FORECAST SUMMARY:\n"
            f"{fcast_json}\n\n"
            f"EVENT DEMAND MULTIPLIERS (≠1.0 only):\n{event_json}\n\n"
            "═══ RESPONSE REQUIREMENTS ═══\n"
            "Produce a procurement plan with 6–8 bullet lines. Each bullet must:\n"
            "  • Name the SKU (use the 'name' field, not sku_id).\n"
            "  • State the order quantity derived as: EOQ × event_multiplier, "
            "rounded to the nearest whole unit.\n"
            "  • State the estimated cost in BDT: quantity × unit_cost_bdt.\n"
            "  • Flag expiry risk if expiry_days ≤ 5.\n"
            "  • Name the supplier from the data.\n"
            "Add ONE final bullet: total estimated procurement budget in BDT "
            "(sum of all line estimates).\n\n"
            "HARD CONSTRAINTS:\n"
            "  - Use only the numbers present in the JSON blocks above.\n"
            "  - Do not recommend ordering any SKU not listed in the low-stock block.\n"
            "  - Do not invent supplier names, prices, or lead times.\n"
            "  - If event_multiplier is absent for a SKU, use ×1.0."
        )

    # ── Private: Rule-based fallbacks ─────────────────────────────────────────

    def _rule_based_market_analysis(
        self, event: str, live_prices: Dict, weather: Dict
    ) -> str:
        rain = weather.get("rain_chance", 0)
        temp = weather.get("temp_c", 30)
        parts: List[str] = []

        if rain > 60:
            parts.append(
                f"Heavy rain probability ({rain}%) will drive a 30–50% surge in "
                f"comfort staples — rice_5kg and lentil_kg EOQ should increase 25% immediately."
            )
        elif temp > 33:
            parts.append(
                f"Heat index at {temp}°C elevates cold-chain demand for chicken and eggs "
                f"by an estimated 15–20%; ensure refrigerated vehicle allocation for peak hours."
            )
        else:
            parts.append(
                f"Weather ({weather.get('condition', 'normal')}, {temp}°C) is stable — "
                f"maintain standard EOQ cadence across all hubs."
            )

        spikes = [
            f"{info.get('name', sid)} ({round(((info.get('price',0)-info.get('prev_price',info.get('price',0)))/max(info.get('prev_price',1),1))*100,1):+.1f}%)"
            for sid, info in live_prices.items()
            if info.get("prev_price", 0) > 0
            and info.get("price", 0) > info.get("prev_price", 0) * 1.05
        ]
        if spikes:
            parts.append(
                f"Price anomalies detected: {', '.join(spikes)} — "
                f"activate competitive pricing review to protect market share."
            )
        else:
            parts.append("No price anomalies detected; all SKU prices within ±5% of prior values.")

        if event != "Normal Day":
            hot  = [SKUS[s][0] for s, f in EVENT_DEMAND_FACTORS.get(event, {}).items() if f > 1.4]
            cold = [SKUS[s][0] for s, f in EVENT_DEMAND_FACTORS.get(event, {}).items() if f < 0.6]
            if hot:
                parts.append(
                    f"Event '{event}' multipliers signal surge demand for: "
                    f"{', '.join(hot[:4])} — pre-stock 40–60% above EOQ before event start."
                )
            if cold:
                parts.append(
                    f"Demand expected to drop for: {', '.join(cold[:3])} during '{event}' — "
                    f"reduce inbound orders to prevent overstock."
                )

        return " ".join(parts) or "Market conditions nominal. Standard operations recommended."

    def _rule_based_sku_analysis(
        self, sku_id: str, sku_data: Dict, forecast: Dict
    ) -> str:
        stock   = sku_data.get("current_stock", 50)
        eoq     = max(sku_data.get("eoq", 50), 1)
        reorder = sku_data.get("reorder_point", 20)
        expiry  = sku_data.get("expiry_days", 30)
        price   = sku_data.get("price", 0)
        cost    = sku_data.get("unit_cost", price)
        peak    = max(forecast.get("forecast", [0]))
        avg     = round(sum(forecast.get("forecast", [0])) / max(len(forecast.get("forecast", [1])), 1), 1)
        margin  = round((price - cost) / max(price, 1) * 100, 1) if price > 0 else 0
        cover   = round(stock / max(avg, 0.1), 1)

        parts: List[str] = []

        if stock < reorder:
            order_qty = eoq - stock
            parts.append(
                f"CRITICAL ORDER: stock={stock} units is below reorder point={reorder}; "
                f"place order for {order_qty} units immediately (EOQ={eoq}, days of cover={cover:.1f}d)."
            )
        elif stock < reorder * 1.3:
            parts.append(
                f"ELEVATED: stock={stock} units approaching reorder point={reorder}; "
                f"schedule replenishment of {eoq - stock} units within 48 h (cover={cover:.1f}d)."
            )
        elif stock > eoq * 2.5:
            excess = stock - eoq
            parts.append(
                f"OVERSTOCK: {stock} units exceeds 2.5× EOQ={eoq}; "
                f"promote {excess} excess units to free working capital."
            )
        else:
            parts.append(
                f"STABLE: stock={stock} units, reorder point={reorder}, EOQ={eoq}, "
                f"cover={cover:.1f} days at avg demand {avg} units/day."
            )

        if margin > 0:
            parts.append(
                f"Gross margin is {margin:.1f}% (price ৳{price:.2f}, cost ৳{cost:.2f}); "
                f"{'margin healthy — no price change required.' if margin >= 15 else 'margin below 15% — review pricing or negotiate supplier cost.'}"
            )

        if expiry <= 2:
            parts.append(
                f"EXPIRY CRITICAL: {expiry}d remaining on {stock} units — apply −30% flash markdown immediately."
            )
        elif expiry <= 5:
            parts.append(
                f"Expiry risk: {expiry}d window — apply 10–15% discount to accelerate turnover."
            )
        elif peak > stock * 0.8:
            parts.append(
                f"Peak demand Day {forecast.get('peak_day',1)} = {peak:.0f} units "
                f"vs current stock {stock} — pre-order {round(peak * 1.2)} units to prevent stockout."
            )

        return " ".join(parts) or "SKU metrics within normal operational parameters."

    def _fallback_procurement(self, low_stock: List[Dict], event: str) -> str:
        if not low_stock:
            return (
                "All SKUs are within acceptable stock levels. "
                "Maintain the regular EOQ ordering cycle."
            )
        event_factors = EVENT_DEMAND_FACTORS.get(event, {})
        lines   = [f"7-Day Procurement Plan [{event}]:"]
        total   = 0.0
        for item in sorted(
            low_stock[:6],
            key=lambda x: x.get("current_stock", 999) / max(x.get("reorder_point", 1), 1),
        ):
            sku    = item.get("sku_id", "")
            name   = item.get("name", sku)
            eoq    = item.get("eoq", 50)
            cost   = item.get("unit_cost", 100)
            stock  = item.get("current_stock", 0)
            rp     = item.get("reorder_point", 20)
            exp    = item.get("expiry_days", 999)
            mult   = event_factors.get(sku, 1.0)
            qty    = round(eoq * mult)
            est    = qty * cost
            total += est
            expiry_flag = f" [EXPIRY {exp}d — PRIORITY]" if exp <= 5 else ""
            lines.append(
                f"  • {name}: order {qty} units "
                f"(stock={stock}, reorder@{rp}, EOQ={eoq}, ×{mult:.2f} event mult) "
                f"— est. ৳{est:,.0f} via {item.get('supplier','TBD')}{expiry_flag}"
            )
        lines.append(f"  • Total estimated procurement budget: ৳{total:,.0f}")
        lines.append("  • Prioritise items with expiry ≤3 days for next inbound slot.")
        return "\n".join(lines)

    # ── Private: Real DB history fetch ───────────────────────────────────────

    def fetch_sales_history_from_db(self, sku_id: str) -> List[float]:
        """
        Pull daily aggregated sold quantities for *sku_id* directly from the
        ``orders`` table and return them as a time-ordered list of floats
        (oldest → newest) with at least ``LOOKBACK`` data points.

        Aggregation:  SUM(quantity) per calendar day, status-agnostic
                      (pending orders count as committed demand).

        Padding strategy when fewer than LOOKBACK days of real data exist:
          • If ≥1 real day exists  → prepend the rolling mean to fill the gap.
          • If 0 real days exist    → return a deterministic flat baseline
                                      derived from the SKU's known reorder point
                                      so that Holt's / LSTM still gets a
                                      meaningful starting level with zero noise.
        """
        if self._db is not None:
            try:
                rows = self._db.fetch_all(
                    "SELECT date(created_at) AS day, SUM(quantity) AS qty "
                    "FROM orders "
                    "WHERE sku_id = ? "
                    "GROUP BY date(created_at) "
                    "ORDER BY day ASC",
                    (sku_id,),
                )
                series: List[float] = [float(r["qty"]) for r in rows if r.get("qty")]
            except Exception as exc:
                self.logger.warning(
                    "fetch_sales_history_from_db(%s) DB error: %s", sku_id, exc
                )
                series = []
        else:
            series = []

        if len(series) >= self.LOOKBACK:
            return series                          # ← real data is sufficient

        if series:
            # Pad the front with the observed daily mean so the level initialises
            # correctly without introducing sine-wave or random artefacts.
            pad_val = sum(series) / len(series)
            padding = [round(pad_val, 1)] * (self.LOOKBACK - len(series))
            return padding + series

        # No orders at all yet — build a flat, deterministic baseline from the
        # SKU's reorder_point (a proxy for minimum viable daily demand).
        return self._flat_baseline(sku_id)

    def _flat_baseline(self, sku_id: str) -> List[float]:
        """
        Deterministic flat demand baseline used only when the orders table has
        no history for *sku_id*.

        Daily demand estimate = reorder_point / 7  (one reorder cycle ≈ 7 days).
        Falls back to 5.0 units/day if reorder_point is unavailable.
        No randomness, no sine waves — purely data-driven constant.
        """
        baseline = 5.0
        if self._db is not None:
            try:
                row = self._db.fetch_one(
                    "SELECT reorder_point FROM inventory WHERE sku_id = ?",
                    (sku_id,),
                )
                if row and row.get("reorder_point"):
                    baseline = max(float(row["reorder_point"]) / 7.0, 1.0)
            except Exception:
                pass
        return [round(baseline, 1)] * (self.LOOKBACK * 3)

    # ── Private: LSTM — background-thread training, non-blocking ─────────────

    def _lstm_forecast(self, sku_id: str, history: List[float]) -> Dict:
        """
        Non-blocking LSTM forecast.

        First call for a given *sku_id*:
          • Launches model.fit() in a daemon background thread.
          • Raises RuntimeError so ``forecast_demand`` falls through to Holt's
            for this render cycle — the UI is never frozen.

        Subsequent calls (same session, after training completes):
          • Returns the cached forecast result instantly from
            ``_lstm_bg_cache`` without re-training.

        The training thread writes its result into the class-level
        ``_lstm_bg_cache`` dict under ``_lstm_bg_lock`` so concurrent
        Streamlit sessions cannot corrupt each other's entries.
        """
        cls = self.__class__

        # ── Fast path: return cached result if training already finished ──────
        with cls._lstm_bg_lock:
            if sku_id in cls._lstm_bg_cache:
                return cls._lstm_bg_cache[sku_id]

            # ── Already training in another thread — fall back this cycle ─────
            if cls._lstm_bg_training.get(sku_id, False):
                raise RuntimeError(
                    f"LSTM training in progress for {sku_id} — Holt's used this cycle"
                )

            # ── First call: kick off background training ──────────────────────
            cls._lstm_bg_training[sku_id] = True

        thread = threading.Thread(
            target  = self._train_lstm_background,
            args    = (sku_id, list(history)),
            daemon  = True,
            name    = f"lstm-train-{sku_id}",
        )
        thread.start()
        self.logger.info(
            "LSTM background training started for %s (thread: %s)", sku_id, thread.name
        )
        raise RuntimeError(
            f"LSTM training dispatched to background for {sku_id} — "
            "Holt's statistical forecast used for this render cycle"
        )

    def _train_lstm_background(self, sku_id: str, history: List[float]) -> None:
        """
        Runs inside a daemon thread.  Trains the LSTM on *history*, stores the
        forecast result in ``_lstm_bg_cache``, and clears the training flag.
        Any exception is caught and logged so the thread never crashes silently.
        """
        cls = self.__class__
        try:
            arr   = np.array(history, dtype=np.float32)
            mu    = float(arr.mean())
            sigma = float(arr.std()) + 1e-6
            norm  = (arr - mu) / sigma

            X_list, y_list = [], []
            for i in range(len(norm) - self.LOOKBACK):
                X_list.append(norm[i: i + self.LOOKBACK])
                y_list.append(norm[i + self.LOOKBACK])

            X = np.array(X_list).reshape(-1, self.LOOKBACK, 1)
            y = np.array(y_list)

            model = self._get_or_build_lstm(sku_id)
            model.fit(X, y, epochs=self.EPOCHS, batch_size=self.BATCH_SIZE, verbose=0)

            # ── Autoregressive multi-step prediction ─────────────────────────
            seq      = list(norm[-self.LOOKBACK:])
            forecast = []
            for _ in range(FORECAST_DAYS):
                inp  = np.array(seq[-self.LOOKBACK:]).reshape(1, self.LOOKBACK, 1)
                pred = float(model.predict(inp, verbose=0)[0, 0])
                forecast.append(pred)
                seq.append(pred)

            denorm   = [max(0.0, round(float(p * sigma + mu), 1)) for p in forecast]
            peak_day = int(np.argmax(denorm)) + 1
            result   = {
                "sku_id":     sku_id,
                "forecast":   denorm,
                "confidence": 0.84,
                "method":     "lstm",
                "peak_day":   peak_day,
            }

            with cls._lstm_bg_lock:
                cls._lstm_bg_cache[sku_id]    = result
                cls._lstm_bg_training[sku_id] = False
                # ── Memory guard: keep only the 8 most recently trained SKUs ──
                if len(cls._lstm_bg_cache) > 8:
                    oldest = next(iter(cls._lstm_bg_cache))
                    del cls._lstm_bg_cache[oldest]

            self.logger.info("LSTM background training complete for %s", sku_id)

        except Exception as exc:
            self.logger.error("LSTM background training failed for %s: %s", sku_id, exc)
            with cls._lstm_bg_lock:
                cls._lstm_bg_training[sku_id] = False   # allow retry next cycle

    def _get_or_build_lstm(self, sku_id: str) -> Any:
        if sku_id in self._models:
            return self._models[sku_id]
        model = Sequential([
            LSTM(self.LSTM_UNITS, input_shape=(self.LOOKBACK, 1), return_sequences=True),
            Dropout(0.2),
            LSTM(32),
            Dropout(0.2),
            Dense(1),
        ])
        model.compile(optimizer=Adam(learning_rate=1e-3), loss="mse")
        self._models[sku_id] = model
        return model

    # ── Private: Holt's Linear Trend — strict statistical implementation ──────

    def _holts_forecast(self, sku_id: str, history: List[float]) -> Dict:
        """
        Holt's Linear Exponential Smoothing (double exponential smoothing).

        Model equations (standard Holt 1957 formulation):
          Level:   L_t = α · y_t  +  (1 − α) · (L_{t-1} + T_{t-1})
          Trend:   T_t = β  · (L_t − L_{t-1})  +  (1 − β) · T_{t-1}
          Forecast: ŷ_{t+h} = L_t + h · T_t

        Parameters:
          α = 0.35  — level smoothing (higher → more reactive to recent demand)
          β = 0.10  — trend smoothing (lower  → trend changes slowly)

        No randomness is introduced at any point.  The forecast is the pure
        deterministic h-step-ahead projection from the final level and trend.
        """
        arr   = [float(v) for v in history[-28:]]   # cap at 28 days for stability
        alpha = 0.35
        beta  = 0.10

        # Initialise level to first observation, trend to overall linear slope
        level = arr[0]
        trend = (arr[-1] - arr[0]) / max(len(arr) - 1, 1)

        for val in arr[1:]:
            prev_level = level
            level      = alpha * val + (1.0 - alpha) * (level + trend)
            trend      = beta  * (level - prev_level) + (1.0 - beta) * trend

        # Pure h-step-ahead projection — no noise, no hash perturbation
        forecast = [
            max(0.0, round(level + trend * (h + 1), 1))
            for h in range(FORECAST_DAYS)
        ]
        peak_day = max(range(FORECAST_DAYS), key=lambda i: forecast[i]) + 1
        return {
            "sku_id":     sku_id,
            "forecast":   forecast,
            "confidence": 0.68,
            "method":     "holts_linear_trend",
            "peak_day":   peak_day,
        }


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 4 ── DECISION SUPPORT SYSTEM (MCDA ENGINE)
# ═══════════════════════════════════════════════════════════════════════════════

class DSSEngine:
    """
    Multi-Criteria Decision Analysis (MCDA) engine.

    Five criteria (each normalised 0-1):
    demand_score, price_score, stock_score, expiry_score, margin_score
    """

    ACTION_THRESHOLDS = {
        "CRITICAL_ORDER": 0.80,
        "URGENT_ORDER":   0.65,
        "MONITOR":        0.45,
        "STABLE":         0.25,
        "OVERSTOCK":      0.00,
    }

    def __init__(self, weights: Optional[Dict[str, float]] = None) -> None:
        self.weights = weights or DEFAULT_DSS_WEIGHTS.copy()
        self.logger  = logging.getLogger(self.__class__.__name__)
        self._validate_weights()

    def rank_skus(self, inventory: List[Dict], forecasts: Dict[str, Dict],
                  prices: Dict[str, Dict]) -> List[Dict]:
        results = []
        for item in inventory:
            sku_id   = item.get("sku_id", "")
            forecast = forecasts.get(sku_id, {})
            p_info   = prices.get(sku_id, {})
            scores   = self._compute_scores(item, forecast, p_info)
            total    = sum(self.weights.get(k, 0) * v for k, v in scores.items())
            total    = round(min(max(total, 0.0), 1.0), 4)
            action   = self.recommend_action(total)
            results.append({
                "sku_id":       sku_id,
                "name":         item.get("name", sku_id),
                "category":     item.get("category", ""),
                **scores,
                "total_score":  total,
                "action":       action,
                "confidence":   forecast.get("confidence", 0.5),
            })
        results.sort(key=lambda x: x["total_score"], reverse=True)
        return results

    def recommend_action(self, total_score: float) -> str:
        if   total_score >= self.ACTION_THRESHOLDS["CRITICAL_ORDER"]: return "CRITICAL_ORDER"
        elif total_score >= self.ACTION_THRESHOLDS["URGENT_ORDER"]:   return "URGENT_ORDER"
        elif total_score >= self.ACTION_THRESHOLDS["MONITOR"]:        return "MONITOR"
        elif total_score >= self.ACTION_THRESHOLDS["STABLE"]:         return "STABLE"
        else:                                                          return "OVERSTOCK"

    def explain_score(self, score_dict: Dict) -> str:
        sku   = score_dict.get("name", score_dict.get("sku_id", "?"))
        total = score_dict.get("total_score", 0)
        act   = score_dict.get("action", "STABLE")
        lines = [f"SKU: {sku}  |  Score: {total:.3f}  |  Action: {act}", ""]
        for crit in ("demand_score","price_score","stock_score","expiry_score","margin_score"):
            val   = score_dict.get(crit, 0)
            label = crit.replace("_score","").title().ljust(10)
            bar   = "█" * int(val * 12) + "░" * (12 - int(val * 12))
            lines.append(f"  {label} {bar} {val:.3f}")
        return "\n".join(lines)

    def update_weights(self, new_weights: Dict[str, float]) -> bool:
        total = sum(new_weights.values())
        if abs(total - 1.0) > 0.02:
            return False
        self.weights = new_weights.copy()
        return True

    def sensitivity_analysis(self, inventory: List[Dict], forecasts: Dict[str, Dict],
                              prices: Dict[str, Dict], n_trials: int = 50) -> Dict[str, Any]:
        rank_counts: Dict[str, Dict[int, int]] = {i["sku_id"]: {} for i in inventory}
        keys = list(DEFAULT_DSS_WEIGHTS.keys())
        for _ in range(n_trials):
            rw   = [abs(random.gauss(0.2, 0.08)) for _ in keys]
            s    = sum(rw) or 1.0
            tw   = {k: rw[i]/s for i, k in enumerate(keys)}
            tmp  = DSSEngine(tw)
            rnkd = tmp.rank_skus(inventory, forecasts, prices)
            for rank, row in enumerate(rnkd, 1):
                sid = row["sku_id"]
                rank_counts[sid][rank] = rank_counts[sid].get(rank, 0) + 1
        return {
            sid: {
                "top_rank_pct": round(100 * cnt.get(1, 0) / n_trials, 1),
                "avg_rank":     round(sum(r*c for r,c in cnt.items()) / max(sum(cnt.values()),1), 1),
            }
            for sid, cnt in rank_counts.items()
        }

    def _compute_scores(self, item: Dict, forecast: Dict, price_inf: Dict) -> Dict[str, float]:
        stock      = item.get("current_stock", 50)
        eoq        = max(item.get("eoq", 50), 1)
        expiry     = item.get("expiry_days", 30)
        unit_cost  = item.get("unit_cost", 0)
        price      = price_inf.get("price", unit_cost) or unit_cost
        prev_price = price_inf.get("prev_price", price) or price
        fcast      = forecast.get("forecast", [50] * FORECAST_DAYS)
        avg_demand = sum(fcast) / max(len(fcast), 1)

        demand_score = min(avg_demand / max(stock, 1) / 3.0, 1.0)

        if prev_price > 0:
            price_score = min(max((((price - prev_price) / prev_price) + 0.2) / 0.4, 0.0), 1.0)
        else:
            price_score = 0.5

        stock_score = min(max(1.0 - (stock / eoq / 3.0), 0.0), 1.0)

        if   expiry <= 1:  expiry_score = 1.0
        elif expiry <= 3:  expiry_score = 0.90
        elif expiry <= 7:  expiry_score = 0.65
        elif expiry <= 14: expiry_score = 0.40
        elif expiry <= 30: expiry_score = 0.20
        else:              expiry_score = 0.05

        if price > 0 and unit_cost > 0:
            margin_score = min(max((price - unit_cost) / price, 0.0), 1.0)
        else:
            margin_score = 0.4

        return {
            "demand_score": round(demand_score,  4),
            "price_score":  round(price_score,   4),
            "stock_score":  round(stock_score,   4),
            "expiry_score": round(expiry_score,  4),
            "margin_score": round(margin_score,  4),
        }

    def _validate_weights(self) -> None:
        total = sum(self.weights.values())
        if abs(total - 1.0) > 0.02:
            factor       = 1.0 / max(total, 1e-9)
            self.weights = {k: v * factor for k, v in self.weights.items()}


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 5 ── BUSINESS OPERATIONS CORE
# ═══════════════════════════════════════════════════════════════════════════════

class BusinessEngine:
    """
    Core business calculations: EOQ, safety stock, dynamic pricing,
    order lifecycle, carbon tracking, auto-alerts, and real revenue analytics.
    """

    CO2_PER_KM_DIESEL   = 0.27
    CO2_PER_KM_ELECTRIC = 0.07
    FUEL_L_PER_KM       = 0.085
    FUEL_PRICE_BDT      = 112

    RIDER_ZONES: Dict[str, List[str]] = {
        "Gulshan":     ["R100","R101","R102"],
        "Dhanmondi":   ["R103","R104","R105"],
        "Mirpur":      ["R106","R107","R108"],
        "Uttara":      ["R109","R110","R111"],
        "Motijheel":   ["R112","R113"],
        "Mohakhali":   ["R114","R115"],
        "Badda":       ["R116","R117"],
        "Rayer Bazar": ["R118","R119"],
        "Wari":        ["R120","R121"],
    }

    def __init__(self, db: "NexusDatabase") -> None:
        self.db     = db
        self.logger = logging.getLogger(self.__class__.__name__)

    # ── EOQ + Safety Stock ────────────────────────────────────────────────────

    def calculate_eoq(self, sku_id: str, annual_demand: float,
                      order_cost: float = 250.0, holding_rate: float = 0.25,
                      unit_cost: float = 0.0) -> Dict[str, float]:
        if unit_cost <= 0:
            inv = self.db.fetch_one("SELECT unit_cost FROM inventory WHERE sku_id=?", (sku_id,))
            unit_cost = (inv or {}).get("unit_cost", 100) or 100
        holding = max(holding_rate * unit_cost, 1.0)
        eoq     = math.sqrt(2 * annual_demand * order_cost / holding)
        orders  = annual_demand / max(eoq, 1)
        return {
            "eoq":               round(eoq, 0),
            "annual_orders":     round(orders, 2),
            "cycle_time_days":   round(365 / max(orders, 0.1), 1),
            "total_annual_cost": round((annual_demand / max(eoq,1)) * order_cost + (eoq/2)*holding, 2),
            "holding_cost_unit": round(holding, 2),
        }

    def calculate_safety_stock(self, avg_daily_demand: float, demand_std: float,
                                lead_time_days: float = 2.0, service_level: float = 0.95) -> Dict[str, float]:
        z_map = {0.90: 1.28, 0.95: 1.645, 0.99: 2.326}
        z     = z_map.get(service_level, 1.645)
        ss    = z * demand_std * math.sqrt(lead_time_days)
        rop   = avg_daily_demand * lead_time_days + ss
        return {
            "safety_stock":   round(ss,  1),
            "reorder_point":  round(rop, 1),
            "z_score":        z,
            "service_level":  service_level,
            "lead_time_days": lead_time_days,
        }

    # ── Dynamic Pricing ───────────────────────────────────────────────────────

    def dynamic_price(self, sku_id: str, base_price: float, stock: int = 50,
                      eoq: int = 50, expiry: int = 30, event: str = "Normal Day") -> Dict[str, Any]:
        factor  = 1.0
        reasons: List[str] = []

        if   expiry <= 1:  factor *= 0.60; reasons.append("60% expiry clearance")
        elif expiry <= 2:  factor *= 0.72; reasons.append("28% expiry discount")
        elif expiry <= 4:  factor *= 0.85; reasons.append("15% expiry markdown")
        elif expiry <= 7:  factor *= 0.93; reasons.append("7% expiry nudge")

        sr = stock / max(eoq, 1)
        if   sr < 0.15: factor *= 1.18; reasons.append("18% scarcity premium")
        elif sr < 0.30: factor *= 1.10; reasons.append("10% low-stock premium")
        elif sr > 2.50: factor *= 0.80; reasons.append("20% overstock clearance")
        elif sr > 1.80: factor *= 0.90; reasons.append("10% overstock discount")

        ef = EVENT_DEMAND_FACTORS.get(event, {}).get(sku_id, 1.0)
        if ef > 1.3:
            factor *= min(ef * 0.85, 1.35)
            reasons.append(f"event demand x{ef:.1f}")

        adjusted = round(base_price * factor, 2)

        # ── Persist to DB whenever a non-trivial adjustment has been applied ──
        if abs(factor - 1.0) > 0.001:
            reason_tag = "; ".join(reasons)
            # 1. Log to price history so the audit trail captures the dynamic price.
            self.db.upsert_price(sku_id, adjusted, base_price, source=f"dynamic:{reason_tag[:60]}")
            # 2. Update selling_price in inventory so GM calculations stay current.
            self.db.execute_query(
                "UPDATE inventory SET selling_price=?, updated_at=datetime('now') WHERE sku_id=?",
                (adjusted, sku_id),
            )
            self.logger.info(
                "dynamic_price persisted for %s: ৳%.2f → ৳%.2f (%s)",
                sku_id, base_price, adjusted, reason_tag,
            )

        return {
            "sku_id":         sku_id,
            "base_price":     base_price,
            "adjusted_price": adjusted,
            "factor":         round(factor, 4),
            "discount_pct":   round((factor - 1.0) * 100, 1),
            "reason":         "; ".join(reasons) or "Standard pricing",
        }

    # ── Order Lifecycle ───────────────────────────────────────────────────────

    def advance_order_status(self, order_id: int) -> str:
        row = self.db.fetch_one("SELECT status FROM orders WHERE order_id=?", (order_id,))
        if not row:
            return "not_found"
        transitions = {"pending":"processing","processing":"in_transit","in_transit":"delivered","delivered":"delivered"}
        new_status  = transitions.get(row["status"], "delivered")
        if new_status == "delivered":
            self.db.execute_query(
                "UPDATE orders SET status=?, delivered_at=datetime('now') WHERE order_id=?",
                (new_status, order_id),
            )
        else:
            self.db.execute_query("UPDATE orders SET status=? WHERE order_id=?", (new_status, order_id))
        return new_status

    def assign_rider(self, order_id: int, zone: str) -> str:
        riders   = self.RIDER_ZONES.get(zone, ["R100"])
        rider_id = random.choice(riders)
        self.db.execute_query("UPDATE orders SET rider_id=? WHERE order_id=?", (rider_id, order_id))
        return rider_id

    def cancel_order(self, order_id: int) -> bool:
        cur = self.db.execute_query(
            "UPDATE orders SET status='cancelled' WHERE order_id=? AND status='pending'", (order_id,)
        )
        return bool(cur and cur.rowcount > 0)

    # ── Carbon ────────────────────────────────────────────────────────────────

    def estimate_carbon(self, km: float, vehicle_type: str = "diesel") -> Dict[str, float]:
        if vehicle_type == "electric":
            return {"co2_kg": round(km*self.CO2_PER_KM_ELECTRIC,3), "fuel_litres":0.0, "cost_bdt": round(km*2.5,2), "km":km}
        fuel = km * self.FUEL_L_PER_KM
        return {"co2_kg": round(km*self.CO2_PER_KM_DIESEL,3), "fuel_litres":round(fuel,3), "cost_bdt":round(fuel*self.FUEL_PRICE_BDT,2), "km":km}

    def calculate_carbon_savings(self, traditional_km: float, optimal_km: float) -> Dict[str, float]:
        saved = traditional_km - optimal_km
        return {
            "km_saved":   round(saved, 2),
            "fuel_saved": round(saved * self.FUEL_L_PER_KM, 3),
            "co2_saved":  round(saved * self.CO2_PER_KM_DIESEL, 3),
            "cost_saved": round(saved * self.FUEL_L_PER_KM * self.FUEL_PRICE_BDT, 2),
            "pct_saving": round(100 * saved / max(traditional_km, 1), 1),
        }

    # ── Auto-alerts ───────────────────────────────────────────────────────────

    def auto_generate_alerts(self, inventory: List[Dict], prices: Dict, weather: Dict) -> int:
        count = 0
        for item in inventory:
            sid, stock, rop, expiry, name = (
                item.get("sku_id",""), item.get("current_stock",999),
                item.get("reorder_point",20), item.get("expiry_days",30),
                item.get("name","?"),
            )
            if stock < rop * 0.5:
                self.db.add_alert("critical","Inventory",
                    f"{name}: stock {stock} CRITICAL (<50% of reorder point {rop})", sid); count += 1
            elif stock < rop:
                self.db.add_alert("warning","Inventory",
                    f"{name}: stock {stock} below reorder point {rop}", sid); count += 1

            if expiry <= 1:
                self.db.add_alert("critical","Expiry",
                    f"{name}: expires in {expiry} day(s) — IMMEDIATE action", sid); count += 1
            elif expiry <= 3:
                self.db.add_alert("warning","Expiry",
                    f"{name}: expires in {expiry} days — promote/discount now", sid); count += 1

        for sid, info in prices.items():
            p, pp = info.get("price",0), info.get("prev_price",0)
            if pp > 0 and p > pp * 1.12:
                pct  = round((p-pp)/pp*100,1)
                self.db.add_alert("warning","Price",
                    f"{info.get('name',sid)} price surged {pct}% (৳{pp}→৳{p}). Review sourcing.", sid)
                count += 1

        rain, temp = weather.get("rain_chance",0), weather.get("temp_c",30)
        if rain > 75:
            self.db.add_alert("warning","Weather",
                f"Heavy rain {rain}% — expect 20-40% delivery delay outer zones."); count += 1
        if temp > 36:
            self.db.add_alert("info","Weather",
                f"Heat alert {temp}°C — prioritise cold-chain for chicken, eggs."); count += 1

        return count

    # ── Revenue analytics (REAL from DB) ─────────────────────────────────────

    def revenue_summary(self) -> Dict[str, Any]:
        stats     = self.db.get_order_stats()
        inv       = self.db.get_inventory()
        daily_raw = self.db.get_daily_revenue(days=7)
        inv_val   = sum(i.get("current_stock",0) * i.get("unit_cost",0) for i in inv)

        # Ensure 7 days of data even if sparse
        today    = datetime.date.today()
        daily    = []
        daily_by_day = {d["day"]: d for d in daily_raw}
        for offset in range(6, -1, -1):
            day_str  = str(today - datetime.timedelta(days=offset))
            day_abbr = (today - datetime.timedelta(days=offset)).strftime("%a")
            d = daily_by_day.get(day_str, {})
            daily.append({
                "day":         day_abbr,
                "date":        day_str,
                "revenue":     round(d.get("revenue") or 0, 2),
                "order_count": d.get("order_count", 0),
            })

        return {
            "total_revenue":   round(stats.get("revenue") or 0, 2),
            "total_orders":    stats.get("total", 0),
            "delivered":       stats.get("delivered", 0),
            "pending":         stats.get("pending", 0),
            "in_transit":      stats.get("in_transit", 0),
            "processing":      stats.get("processing", 0),
            "inventory_value": round(inv_val, 2),
            "daily":           daily,
        }

    def sku_performance(self, inventory: List[Dict], prices: Dict) -> List[Dict]:
        out = []
        for item in inventory:
            sid   = item.get("sku_id","")
            cost  = item.get("unit_cost", 0)          # ← procurement cost (static)
            # Prefer live scraped price, then DB selling_price, then cost+15% fallback
            sell  = (prices.get(sid, {}).get("price")
                     or item.get("selling_price")
                     or cost * 1.15)
            price = sell or (cost * 1.15)
            stock = item.get("current_stock", 0)
            margin= round((price - cost) / max(price, 1) * 100, 1) if price else 0
            out.append({
                "sku_id":        sid,
                "name":          item.get("name", sid),
                "category":      item.get("category",""),
                "sell_price":    round(price, 2),
                "unit_cost":     round(cost, 2),
                "gross_margin":  margin,
                "stock_value":   round(stock * cost, 2),
                "potential_gp":  round((price - cost) * stock, 2),
                "data_source":   prices.get(sid, {}).get("data_source","?"),
            })
        out.sort(key=lambda x: x["gross_margin"], reverse=True)
        return out


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 6 ── LOGISTICS & GIS ENGINE
# ═══════════════════════════════════════════════════════════════════════════════

class RoutingEngine:
    """
    Advanced delivery routing engine.

    Routing priority:
    ─────────────────
    1. OSRM (Open Source Routing Machine) public API — real road geometry,
       actual distance & ETA, returns polyline for map rendering.
    2. NetworkX Dijkstra on hardcoded HUB_EDGES — fallback when OSRM unavailable.
    3. Haversine straight-line — last resort when networkx not installed.
    """

    AVG_SPEED_KMH    = 25.0
    VEHICLE_CAPACITY = 30
    OSRM_BASE        = "http://router.project-osrm.org/route/v1/driving"
    OSRM_TIMEOUT     = 6   # seconds — keep UI responsive

    def __init__(self) -> None:
        self.logger       = logging.getLogger(self.__class__.__name__)
        self._closed_hubs: set = set()

    # ── OSRM real-time routing ─────────────────────────────────────────────────

    def _osrm_route(self, origin: Tuple[float, float], destination: Tuple[float, float]) -> Optional[Dict]:
        """
        Call OSRM public demo server for a real road route.
        Returns dict with distance_km, duration_min, route_coords (list of [lat,lon]).
        Returns None on any failure so callers can fall back gracefully.
        """
        if not BS4_AVAILABLE:          # reuse requests availability flag
            return None
        try:
            lat1, lon1 = origin
            lat2, lon2 = destination
            url = (
                f"{self.OSRM_BASE}/{lon1},{lat1};{lon2},{lat2}"
                f"?overview=full&geometries=polyline"
            )
            resp = requests.get(url, timeout=self.OSRM_TIMEOUT)
            data = resp.json()
            if data.get("code") != "Ok":
                return None
            route_info = data["routes"][0]
            distance_km  = round(route_info["distance"] / 1000.0, 2)
            duration_min = round(route_info["duration"] / 60.0, 1)
            encoded      = route_info["geometry"]
            # Decode polyline → list of [lat, lon]
            if POLYLINE_AVAILABLE:
                route_coords = _polyline_lib.decode(encoded)
            else:
                # Minimal inline decoder for polyline5 format
                route_coords = self._decode_polyline(encoded)
            return {
                "distance_km":  distance_km,
                "duration_min": duration_min,
                "route_coords": route_coords,   # list of (lat, lon) tuples
            }
        except Exception as exc:
            self.logger.warning("OSRM call failed: %s", exc)
            return None

    @staticmethod
    def _decode_polyline(encoded: str) -> List[Tuple[float, float]]:
        """Inline polyline5 decoder (no external library needed)."""
        coords, idx, lat, lng = [], 0, 0, 0
        while idx < len(encoded):
            for coord_ref in [lat, lng]:
                result, shift, b = 0, 0, 0
                while True:
                    if idx >= len(encoded):
                        break
                    b = ord(encoded[idx]) - 63
                    idx += 1
                    result |= (b & 0x1F) << shift
                    shift  += 5
                    if b < 0x20:
                        break
                coord_change = ~(result >> 1) if (result & 1) else (result >> 1)
                if coord_ref is lat:
                    lat += coord_change
                else:
                    lng += coord_change
            coords.append((lat / 1e5, lng / 1e5))
        return coords

    def find_optimal_route(self, source: str, target: str, mode: str = "balanced") -> Dict[str, Any]:
        src_coords = DHAKA_HUBS.get(source)
        dst_coords = DHAKA_HUBS.get(target)

        # ── Try OSRM first ─────────────────────────────────────────────────────
        osrm_result = None
        if src_coords and dst_coords and mode != "distance":
            osrm_result = self._osrm_route(src_coords, dst_coords)

        if osrm_result:
            trad_km = osrm_result["distance_km"] * 1.30
            savings = self._savings(trad_km, osrm_result["distance_km"])
            return {
                "path":            [source, target],
                "total_km":        osrm_result["distance_km"],
                "eta_min":         osrm_result["duration_min"],
                "traffic_factor":  round(osrm_result["duration_min"] /
                                         max((osrm_result["distance_km"] / self.AVG_SPEED_KMH * 60), 1), 2),
                "hops":            1,
                "traditional_km":  round(trad_km, 2),
                "co2_saving_kg":   savings["co2_saved"],
                "cost_saving_bdt": savings["cost_saved"],
                "mode":            "osrm_realtime",
                "route_coords":    osrm_result["route_coords"],   # ← real road polyline
                "data_source":     "OSRM",
            }

        # ── Fallback: NetworkX Dijkstra on HUB_EDGES ──────────────────────────
        if not NX_AVAILABLE:
            return self._haversine_route(source, target)
        G = self._build_graph(mode=mode)
        try:
            path = nx.dijkstra_path(G, source, target, weight="weight")
        except (nx.NetworkXNoPath, nx.NodeNotFound):
            G2 = G.copy()
            for h in self._closed_hubs - {source, target}:
                if G2.has_node(h): G2.remove_node(h)
            try:
                path = nx.dijkstra_path(G2, source, target, weight="weight")
            except Exception:
                return {"error": f"No route: {source} → {target} (hubs closed: {list(self._closed_hubs)})"}

        total_km, traffic_sum = 0.0, 0.0
        hops = len(path) - 1
        for i in range(hops):
            km, tr  = self._edge_attrs(path[i], path[i+1])
            total_km += km; traffic_sum += tr

        avg_traffic = traffic_sum / max(hops, 1)
        eta_min     = round((total_km / self.AVG_SPEED_KMH) * avg_traffic * 60, 1)
        trad_km     = total_km * 1.30
        savings     = self._savings(trad_km, total_km)

        return {
            "path":            path,
            "total_km":        round(total_km, 2),
            "eta_min":         eta_min,
            "traffic_factor":  round(avg_traffic, 2),
            "hops":            hops,
            "traditional_km":  round(trad_km, 2),
            "co2_saving_kg":   savings["co2_saved"],
            "cost_saving_bdt": savings["cost_saved"],
            "mode":            mode,
            "data_source":     "NetworkX",
        }

    def plan_multi_stop(self, hubs: List[str], optimize: bool = True) -> Dict[str, Any]:
        if len(hubs) < 2:
            return {"error": "Need at least 2 hubs"}
        order = self._nn_tsp(hubs) if (optimize and len(hubs) >= 3) else hubs[:]
        legs, total_km, total_eta, total_co2 = [], 0.0, 0.0, 0.0
        for i in range(len(order)-1):
            leg = self.find_optimal_route(order[i], order[i+1])
            if "error" not in leg:
                legs.append(leg); total_km += leg["total_km"]
                total_eta += leg["eta_min"]; total_co2 += leg.get("co2_saving_kg",0)
        return {
            "route_order": order, "legs": legs,
            "total_km": round(total_km,2), "total_eta_min": round(total_eta,1),
            "total_co2_kg": round(total_co2,3), "stops": len(order),
        }

    def close_hub(self, hub: str) -> bool:
        if hub in DHAKA_HUBS:
            self._closed_hubs.add(hub); return True
        return False

    def reopen_hub(self, hub: str) -> bool:
        self._closed_hubs.discard(hub); return hub in DHAKA_HUBS

    def get_closed_hubs(self) -> List[str]:
        return list(self._closed_hubs)

    def get_hub_metrics(self) -> List[Dict]:
        if not NX_AVAILABLE:
            return [{"hub":h,"degree":2,"centrality":0.5,"status":"OPEN" if h not in self._closed_hubs else "CLOSED"} for h in DHAKA_HUBS]
        G    = self._build_graph()
        deg  = dict(G.degree())
        try:    cent = nx.betweenness_centrality(G, weight="weight", normalized=True)
        except: cent = {h: 0.5 for h in DHAKA_HUBS}
        return [{"hub":h,"degree":deg.get(h,0),"centrality":round(cent.get(h,0),4),
                 "status":"CLOSED" if h in self._closed_hubs else "OPEN",
                 "lat":DHAKA_HUBS[h][0],"lon":DHAKA_HUBS[h][1]} for h in DHAKA_HUBS]

    def _build_graph(self, mode: str = "balanced"):
        G = nx.DiGraph()
        G.add_nodes_from(DHAKA_HUBS.keys())
        for a, b, km, tr in HUB_EDGES:
            if a in self._closed_hubs or b in self._closed_hubs:
                continue
            w = km if mode=="distance" else (km*tr if mode=="time" else km*(tr**0.7))
            G.add_edge(a, b, weight=w, km=km, traffic=tr)
            G.add_edge(b, a, weight=w, km=km, traffic=tr)
        return G

    def _edge_attrs(self, a: str, b: str) -> Tuple[float, float]:
        for u, v, km, tr in HUB_EDGES:
            if (u==a and v==b) or (u==b and v==a): return km, tr
        return self._haversine_km(a, b), 1.3

    def _haversine_km(self, a: str, b: str) -> float:
        p1, p2 = DHAKA_HUBS.get(a,(23.78,90.40)), DHAKA_HUBS.get(b,(23.73,90.42))
        R = 6371.0
        lat1,lon1 = math.radians(p1[0]), math.radians(p1[1])
        lat2,lon2 = math.radians(p2[0]), math.radians(p2[1])
        a_ = math.sin((lat2-lat1)/2)**2 + math.cos(lat1)*math.cos(lat2)*math.sin((lon2-lon1)/2)**2
        return R * 2 * math.asin(math.sqrt(a_))

    def _haversine_route(self, source: str, target: str) -> Dict[str, Any]:
        km = self._haversine_km(source, target)
        return {"path":[source,target],"total_km":round(km,2),"eta_min":round(km/self.AVG_SPEED_KMH*1.3*60,1),
                "traffic_factor":1.3,"hops":1,"mode":"haversine","traditional_km":round(km*1.3,2),
                "co2_saving_kg":round(km*0.3*0.27,3),"cost_saving_bdt":round(km*0.3*0.085*112,2)}

    def _savings(self, trad: float, opt: float) -> Dict[str, float]:
        s = trad - opt
        return {"co2_saved":round(s*0.27,3),"cost_saved":round(s*0.085*112,2)}

    def _nn_tsp(self, hubs: List[str]) -> List[str]:
        unvisited = hubs[1:]; route = [hubs[0]]
        while unvisited:
            cur     = route[-1]
            nearest = min(unvisited, key=lambda h: self._haversine_km(cur, h))
            route.append(nearest); unvisited.remove(nearest)
        return route


# ─────────────────────────────────────────────────────────────────────────────

# ─────────────────────────────────────────────────────────────────────────────

class MapRenderer:
    """
    Folium-based interactive map renderer for LOGIX v7.0.
    Requires: pip install folium streamlit-folium
    """

    DHAKA_CENTER  = [23.7808, 90.4007]
    DEFAULT_ZOOM  = 12
    TILE_PROVIDER = "CartoDB dark_matter"

    COLORS = {
        "hub_open":    "#00ff88",
        "hub_closed":  "#ff3366",
        "route":       "#00cfff",
        "route_alt":   "#ffbb00",
        "edge_low":    "#2a9d8f",
        "edge_mid":    "#e9c46a",
        "edge_high":   "#e76f51",
        "bubble":      "#ff6b35",
        "rider":       "#c084fc",
        "revenue_low": "#1a6b3a",
        "revenue_hi":  "#00ff88",
        "bg":          "#0a0e1a",
        "grid":        "#1a2235",
    }

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)
        self._folium_available = False
        self._fl         = None
        self._fl_plugins = None
        try:
            import folium as _fl
            import folium.plugins as _fl_plugins
            self._fl         = _fl
            self._fl_plugins = _fl_plugins
            self._folium_available = True
            self.logger.info("folium ready")
        except ImportError:
            self.logger.warning("folium not installed. Run: pip install folium streamlit-folium")

    # ── Internal helpers ──────────────────────────────────────────────────────

    def _base_map(self, zoom: int = 12) -> Any:
        m = self._fl.Map(
            location      = self.DHAKA_CENTER,
            zoom_start    = zoom,
            tiles         = self.TILE_PROVIDER,
            prefer_canvas = True,
            control_scale = True,
        )
        return m

    def _unavailable_map(self) -> None:
        st.warning(
            "**folium** is not installed. Maps are unavailable.\n\n"
            "Install with: `pip install folium streamlit-folium`"
        )

    @staticmethod
    def _hex_to_rgb(hex_color: str) -> Tuple[int, int, int]:
        h = hex_color.lstrip("#")
        return (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16))

    @staticmethod
    def _interpolate_color(ratio: float, low: str, high: str) -> str:
        r1, g1, b1 = MapRenderer._hex_to_rgb(low)
        r2, g2, b2 = MapRenderer._hex_to_rgb(high)
        r = int(r1 + (r2 - r1) * ratio)
        g = int(g1 + (g2 - g1) * ratio)
        b = int(b1 + (b2 - b1) * ratio)
        return f"#{r:02x}{g:02x}{b:02x}"

    @staticmethod
    def _traffic_color(traffic: float) -> str:
        if traffic < 1.3:
            return MapRenderer.COLORS["edge_low"]
        if traffic < 1.6:
            return MapRenderer.COLORS["edge_mid"]
        return MapRenderer.COLORS["edge_high"]

    @staticmethod
    def _traffic_label(traffic: float) -> str:
        if traffic < 1.3:
            return "Low"
        if traffic < 1.6:
            return "Moderate"
        return "Heavy"

    # ── Public API ────────────────────────────────────────────────────────────

    def render_hub_map(
        self,
        hub_metrics:  List[Dict],
        route_result: Optional[Dict]      = None,
        closed_hubs:  Optional[List[str]] = None,
    ) -> Any:
        if not self._folium_available:
            self._unavailable_map()
            return None

        fl     = self._fl
        m      = self._base_map(zoom=12)
        closed = set(closed_hubs or [])

        # Layer 1: hub edges
        edge_layer = fl.FeatureGroup(name="Hub Edges", show=True)
        for hub_a, hub_b, km, traffic in HUB_EDGES:
            if hub_a not in DHAKA_HUBS or hub_b not in DHAKA_HUBS:
                continue
            color   = self._traffic_color(traffic)
            t_label = self._traffic_label(traffic)
            fl.PolyLine(
                locations = [list(DHAKA_HUBS[hub_a]), list(DHAKA_HUBS[hub_b])],
                color     = color,
                weight    = 2.5,
                opacity   = 0.75,
                tooltip   = (
                    f"<b>{hub_a} to {hub_b}</b><br>"
                    f"Distance: {km} km<br>"
                    f"Traffic: x{traffic} ({t_label})"
                ),
            ).add_to(edge_layer)
        edge_layer.add_to(m)

        # Layer 2: active route overlay
        if route_result and "path" in route_result and len(route_result["path"]) >= 2:
            path_coords = [
                list(DHAKA_HUBS[h])
                for h in route_result["path"]
                if h in DHAKA_HUBS
            ]
            # Prefer real OSRM road polyline over straight hub-to-hub line
            osrm_coords = route_result.get("route_coords")
            draw_coords = [[lat, lon] for lat, lon in osrm_coords] if osrm_coords else path_coords
            data_src    = route_result.get("data_source", "NetworkX")

            if len(draw_coords) >= 2:
                route_layer = fl.FeatureGroup(name="Active Route", show=True)
                fl.PolyLine(
                    locations  = draw_coords,
                    color      = self.COLORS["route"],
                    weight     = 5,
                    opacity    = 0.95,
                    dash_array = "10 6",
                    tooltip    = (
                        f"<b>Optimal Route [{data_src}]</b><br>"
                        f"Path: {' > '.join(route_result.get('path', []))}<br>"
                        f"Dist: {route_result.get('total_km', '?')} km<br>"
                        f"ETA: {route_result.get('eta_min', '?')} min"
                    ),
                ).add_to(route_layer)
                try:
                    self._fl_plugins.AntPath(
                        locations   = draw_coords,
                        color       = self.COLORS["route"],
                        weight      = 4,
                        delay       = 800,
                        pulse_color = "#ffffff",
                    ).add_to(route_layer)
                except Exception:
                    pass
                for coord in [draw_coords[0], draw_coords[-1]]:
                    fl.CircleMarker(
                        location     = coord,
                        radius       = 10,
                        color        = self.COLORS["route"],
                        fill         = True,
                        fill_color   = "#ffffff",
                        fill_opacity = 0.95,
                    ).add_to(route_layer)
                route_layer.add_to(m)

        # Layer 3: hub markers
        hub_layer     = fl.FeatureGroup(name="Hubs", show=True)
        metric_by_hub = {hm["hub"]: hm for hm in hub_metrics}

        for hub_name, (lat, lon) in DHAKA_HUBS.items():
            hm         = metric_by_hub.get(hub_name, {})
            is_closed  = hub_name in closed
            centrality = hm.get("centrality", 0.3)
            degree     = hm.get("degree", 2)
            radius     = max(9, min(int(10 + centrality * 20), 26))
            fill_color = self.COLORS["hub_closed"] if is_closed else self.COLORS["hub_open"]
            status_txt = "CLOSED" if is_closed else "OPEN"

            popup_html = (
                "<div style='font-family:monospace;min-width:160px;'>"
                f"<b>{hub_name}</b><br>"
                f"<span style='color:{fill_color};'>{status_txt}</span><br>"
                f"Betweenness: <b>{centrality:.4f}</b><br>"
                f"Connections: <b>{degree}</b><br>"
                f"{lat:.4f}N, {lon:.4f}E"
                "</div>"
            )
            fl.CircleMarker(
                location     = [lat, lon],
                radius       = radius,
                color        = fill_color,
                weight       = 2,
                fill         = True,
                fill_color   = fill_color,
                fill_opacity = 0.80,
                popup        = fl.Popup(popup_html, max_width=220),
                tooltip      = f"<b>{hub_name}</b> [{status_txt}] | centrality: {centrality:.3f}",
            ).add_to(hub_layer)
            fl.Marker(
                location = [lat + 0.0015, lon],
                icon     = fl.DivIcon(
                    html=(
                        "<div style='font-family:monospace;font-size:10px;"
                        f"font-weight:700;color:{fill_color};"
                        "text-shadow:0 0 4px #000;white-space:nowrap;'>"
                        f"{'X ' if is_closed else ''}{hub_name}</div>"
                    ),
                    icon_size   = (100, 16),
                    icon_anchor = (50, 8),
                ),
            ).add_to(hub_layer)

        hub_layer.add_to(m)
        fl.LayerControl(collapsed=False).add_to(m)

        legend_html = (
            "<div style='position:fixed;bottom:30px;left:30px;z-index:1000;"
            "background:rgba(10,14,26,0.90);border:1px solid #1e3a5f;"
            "border-radius:8px;padding:10px 14px;font-family:monospace;"
            "font-size:12px;color:#7dd3fc;'>"
            "<b>Hub Network</b><br>"
            f"<span style='color:{self.COLORS['hub_open']}'>Open hub</span><br>"
            f"<span style='color:{self.COLORS['hub_closed']}'>Closed hub</span><br>"
            f"<span style='color:{self.COLORS['edge_low']}'>Low traffic</span><br>"
            f"<span style='color:{self.COLORS['edge_mid']}'>Moderate traffic</span><br>"
            f"<span style='color:{self.COLORS['edge_high']}'>Heavy traffic</span>"
            "</div>"
        )
        m.get_root().html.add_child(fl.Element(legend_html))
        return m

    def render_demand_bubbles(
        self,
        inventory: List[Dict],
        forecasts: Dict[str, Dict],
        prices:    Dict[str, Dict],
    ) -> Any:
        if not self._folium_available:
            self._unavailable_map()
            return None

        fl = self._fl
        m  = self._base_map(zoom=12)

        zone_demand:  Dict[str, float]     = {}
        zone_details: Dict[str, List[str]] = {}

        for hub in DHAKA_HUBS:
            seed_r  = random.Random(sum(ord(c) for c in hub))
            total   = 0.0
            details = []
            for item in inventory:
                sid   = item.get("sku_id", "")
                name  = item.get("name", sid)
                fcast = forecasts.get(sid, {}).get("forecast", [50] * FORECAST_DAYS)
                avg_d = sum(fcast) / max(len(fcast), 1)
                price = prices.get(sid, {}).get("price", 50) or 50
                val   = avg_d * price * seed_r.uniform(0.65, 1.35)
                total += val
                details.append(f"{name}: {avg_d:.1f} u/day x {price:.0f}")
            zone_demand[hub]  = total
            zone_details[hub] = details

        max_demand   = max(zone_demand.values()) or 1.0
        bubble_layer = fl.FeatureGroup(name="Demand Bubbles", show=True)

        for hub_name, (lat, lon) in DHAKA_HUBS.items():
            demand = zone_demand.get(hub_name, 0)
            ratio  = demand / max_demand
            radius       = max(12, min(int(15 + ratio * 50), 65))
            fill_opacity = 0.20 + ratio * 0.55
            color        = self._interpolate_color(ratio, "#7b2d00", self.COLORS["bubble"])

            detail_lines = "<br>".join(zone_details.get(hub_name, []))
            popup_html   = (
                "<div style='font-family:monospace;min-width:200px;'>"
                f"<b>{hub_name}</b><br>"
                f"<b style='color:{self.COLORS['bubble']};'>Demand: {demand:,.0f}</b> "
                f"({ratio*100:.1f}% of peak)<br><hr>{detail_lines}</div>"
            )
            fl.CircleMarker(
                location     = [lat, lon],
                radius       = radius + 10,
                color        = color,
                weight       = 1,
                fill         = True,
                fill_color   = color,
                fill_opacity = 0.06,
            ).add_to(bubble_layer)
            fl.CircleMarker(
                location     = [lat, lon],
                radius       = radius,
                color        = color,
                weight       = 2,
                fill         = True,
                fill_color   = color,
                fill_opacity = fill_opacity,
                popup        = fl.Popup(popup_html, max_width=260),
                tooltip      = f"<b>{hub_name}</b> | Demand: {demand:,.0f} ({ratio*100:.1f}%)",
            ).add_to(bubble_layer)
            fl.Marker(
                location = [lat + 0.0018, lon],
                icon     = fl.DivIcon(
                    html=(
                        "<div style='font-family:monospace;font-size:10px;font-weight:700;"
                        f"color:{color};text-shadow:0 0 4px #000;white-space:nowrap;"
                        f"text-align:center;'>{hub_name}</div>"
                    ),
                    icon_size   = (100, 16),
                    icon_anchor = (50, 8),
                ),
            ).add_to(bubble_layer)

        bubble_layer.add_to(m)
        fl.LayerControl(collapsed=False).add_to(m)

        legend_html = (
            "<div style='position:fixed;bottom:30px;left:30px;z-index:1000;"
            "background:rgba(10,14,26,0.90);border:1px solid #1e3a5f;"
            "border-radius:8px;padding:10px 14px;font-family:monospace;"
            "font-size:12px;color:#7dd3fc;'>"
            "<b>Demand Bubble Map</b><br>"
            f"<span style='color:{self.COLORS['bubble']}'>Large + bright = high demand</span><br>"
            "<i>Click bubble for SKU breakdown</i>"
            "</div>"
        )
        m.get_root().html.add_child(fl.Element(legend_html))
        return m

    def render_rider_map(self, orders: List[Dict]) -> Any:
        if not self._folium_available:
            self._unavailable_map()
            return None

        fl        = self._fl
        m         = self._base_map(zoom=12)
        zone_cnt: Dict[str, int]   = defaultdict(int)
        zone_rev: Dict[str, float] = defaultdict(float)

        for o in orders:
            z = o.get("zone", "Gulshan")
            zone_cnt[z] += 1
            zone_rev[z] += o.get("quantity", 1) * o.get("unit_price", 0)

        if not zone_cnt:
            for h in DHAKA_HUBS:
                zone_cnt[h] = 0

        max_cnt      = max(zone_cnt.values()) or 1
        color        = self.COLORS["rider"]
        rider_layer  = fl.FeatureGroup(name="Rider Distribution", show=True)

        for hub_name, (lat, lon) in DHAKA_HUBS.items():
            cnt     = zone_cnt.get(hub_name, 0)
            rev     = zone_rev.get(hub_name, 0.0)
            ratio   = cnt / max_cnt
            radius  = max(8, min(int(10 + ratio * 35), 48))
            opacity = 0.35 + ratio * 0.50

            popup_html = (
                "<div style='font-family:monospace;'>"
                f"<b>{hub_name}</b><br>"
                f"Orders: <b>{cnt}</b><br>"
                f"Revenue: <b>{rev:,.0f}</b>"
                "</div>"
            )
            fl.CircleMarker(
                location     = [lat, lon],
                radius       = radius,
                color        = color,
                weight       = 2,
                fill         = True,
                fill_color   = color,
                fill_opacity = opacity,
                popup        = fl.Popup(popup_html, max_width=200),
                tooltip      = f"<b>{hub_name}</b> | {cnt} orders | {rev:,.0f}",
            ).add_to(rider_layer)
            fl.Marker(
                location = [lat + 0.0016, lon],
                icon     = fl.DivIcon(
                    html=(
                        "<div style='font-family:monospace;font-size:10px;font-weight:700;"
                        f"color:{color};text-shadow:0 0 4px #000;white-space:nowrap;"
                        f"text-align:center;'>{hub_name} ({cnt})</div>"
                    ),
                    icon_size   = (120, 16),
                    icon_anchor = (60, 8),
                ),
            ).add_to(rider_layer)

        rider_layer.add_to(m)
        fl.LayerControl(collapsed=False).add_to(m)

        legend_html = (
            "<div style='position:fixed;bottom:30px;left:30px;z-index:1000;"
            "background:rgba(10,14,26,0.90);border:1px solid #1e3a5f;"
            "border-radius:8px;padding:10px 14px;font-family:monospace;"
            "font-size:12px;color:#7dd3fc;'>"
            "<b>Rider Distribution</b><br>"
            f"<span style='color:{color}'>Circle size = order count per zone</span>"
            "</div>"
        )
        m.get_root().html.add_child(fl.Element(legend_html))
        return m

    def render_zone_revenue(self, zone_stats: List[Dict]) -> Any:
        if not self._folium_available:
            self._unavailable_map()
            return None
        if not zone_stats:
            return self.render_rider_map([])

        fl      = self._fl
        m       = self._base_map(zoom=12)
        max_rev = max((z.get("revenue") or 0) for z in zone_stats) or 1.0
        rev_layer = fl.FeatureGroup(name="Zone Revenue", show=True)

        for z in zone_stats:
            zone_name = z.get("zone", "?")
            revenue   = float(z.get("revenue") or 0)
            orders    = z.get("orders", 0)
            if zone_name not in DHAKA_HUBS:
                continue
            lat, lon = DHAKA_HUBS[zone_name]
            ratio    = revenue / max_rev
            radius   = max(10, min(int(12 + ratio * 45), 55))
            color    = self._interpolate_color(
                ratio, self.COLORS["revenue_low"], self.COLORS["revenue_hi"]
            )
            opacity  = 0.40 + ratio * 0.45

            popup_html = (
                "<div style='font-family:monospace;'>"
                f"<b>{zone_name}</b><br>"
                f"Revenue: <b style='color:{color};'>{revenue:,.0f}</b><br>"
                f"Orders: <b>{orders}</b>"
                "</div>"
            )
            fl.CircleMarker(
                location     = [lat, lon],
                radius       = radius,
                color        = color,
                weight       = 2,
                fill         = True,
                fill_color   = color,
                fill_opacity = opacity,
                popup        = fl.Popup(popup_html, max_width=200),
                tooltip      = f"<b>{zone_name}</b> | {revenue:,.0f} ({orders} orders)",
            ).add_to(rev_layer)
            fl.Marker(
                location = [lat + 0.0016, lon],
                icon     = fl.DivIcon(
                    html=(
                        "<div style='font-family:monospace;font-size:10px;font-weight:700;"
                        f"color:{color};text-shadow:0 0 4px #000;white-space:nowrap;"
                        f"text-align:center;'>{zone_name}</div>"
                    ),
                    icon_size   = (110, 16),
                    icon_anchor = (55, 8),
                ),
            ).add_to(rev_layer)

        rev_layer.add_to(m)
        fl.LayerControl(collapsed=False).add_to(m)

        legend_html = (
            "<div style='position:fixed;bottom:30px;left:30px;z-index:1000;"
            "background:rgba(10,14,26,0.90);border:1px solid #1e3a5f;"
            "border-radius:8px;padding:10px 14px;font-family:monospace;"
            "font-size:12px;color:#7dd3fc;'>"
            "<b>Zone Revenue</b><br>"
            f"<span style='color:{self.COLORS['revenue_hi']}'>Bright = high revenue</span><br>"
            f"<span style='color:{self.COLORS['revenue_low']}'>Dark = low revenue</span>"
            "</div>"
        )
        m.get_root().html.add_child(fl.Element(legend_html))
        return m


# ═══════════════════════════════════════════════════════════════════════════════
# ADVANCED GIS MODULE A ── PYDECK 3D/ARC MAP RENDERER (Deck.gl WebGL)
# ═══════════════════════════════════════════════════════════════════════════════

class PyDeckRenderer:
    """
    WebGL-powered advanced map renderer using PyDeck (Deck.gl by Uber).

    Advantages over Folium:
    • Renders thousands of data points without UI lag (GPU-accelerated)
    • ArcLayer — animated 3D arcs between delivery hubs
    • ScatterplotLayer — demand bubbles with GPU interpolation
    • ColumnLayer  — 3D revenue columns per zone
    • HexagonLayer — density heatmap for order clusters

    Requirements:  pip install pydeck
    """

    DHAKA_CENTER = {"longitude": 90.4007, "latitude": 23.7808, "zoom": 11, "pitch": 45}

    COLORS_RGB = {
        "hub_open":  [0,  255, 136],    # #00ff88
        "hub_closed":[255, 51, 102],    # #ff3366
        "arc_src":   [0,  207, 255],    # #00cfff
        "arc_dst":   [255, 187,  0],    # #ffbb00
        "demand":    [255, 107,  53],   # #ff6b35
        "revenue":   [0,  255, 136],    # #00ff88
        "rider":     [192, 132, 252],   # #c084fc
    }

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)

    def _not_available(self) -> None:
        st.warning(
            "**pydeck** is not installed. Run: `pip install pydeck`\n\n"
            "Falling back to Folium maps."
        )

    # ── Hub Arc Map ────────────────────────────────────────────────────────────

    def render_arc_map(
        self,
        hub_metrics:  List[Dict],
        route_result: Optional[Dict] = None,
        closed_hubs:  Optional[List[str]] = None,
    ) -> None:
        """
        Renders an animated 3D arc map.
        Each hub edge is drawn as a curved arc coloured by traffic.
        Active route arcs are highlighted in bright cyan.
        """
        if not PYDECK_AVAILABLE:
            self._not_available(); return

        closed = set(closed_hubs or [])
        metric_map = {hm["hub"]: hm for hm in hub_metrics}

        # ── ScatterplotLayer: hub nodes ───────────────────────────────────────
        hub_data = []
        for name, (lat, lon) in DHAKA_HUBS.items():
            hm = metric_map.get(name, {})
            is_closed = name in closed
            centrality = hm.get("centrality", 0.3)
            hub_data.append({
                "name":       name,
                "coordinates":[lon, lat],
                "color":      self.COLORS_RGB["hub_closed"] if is_closed
                              else self.COLORS_RGB["hub_open"],
                "radius":     int(200 + centrality * 600),
                "status":     "CLOSED" if is_closed else "OPEN",
            })

        scatter_layer = pdk.Layer(
            "ScatterplotLayer",
            hub_data,
            get_position="coordinates",
            get_color="color",
            get_radius="radius",
            pickable=True,
            opacity=0.85,
            stroked=True,
            filled=True,
            radius_min_pixels=6,
            radius_max_pixels=30,
        )

        # ── ArcLayer: hub edges ────────────────────────────────────────────────
        arc_data = []
        active_path = set()
        if route_result and "path" in route_result:
            p = route_result["path"]
            for i in range(len(p) - 1):
                active_path.add((p[i], p[i+1]))
                active_path.add((p[i+1], p[i]))

        for hub_a, hub_b, km, traffic in HUB_EDGES:
            if hub_a not in DHAKA_HUBS or hub_b not in DHAKA_HUBS:
                continue
            is_active = (hub_a, hub_b) in active_path
            if traffic < 1.3:
                color = [42, 157, 143]       # green-teal — low traffic
            elif traffic < 1.6:
                color = [233, 196, 106]      # amber — moderate
            else:
                color = [231, 111,  81]      # red-orange — heavy
            if is_active:
                color = [0, 207, 255]        # bright cyan — active route

            la, loa = DHAKA_HUBS[hub_a]
            lb, lob = DHAKA_HUBS[hub_b]
            arc_data.append({
                "from": {"coordinates": [loa, la]},
                "to":   {"coordinates": [lob, lb]},
                "color": color,
                "label": f"{hub_a}→{hub_b}: {km}km x{traffic}",
                "is_active": is_active,
            })

        arc_layer = pdk.Layer(
            "ArcLayer",
            arc_data,
            get_source_position="from.coordinates",
            get_target_position="to.coordinates",
            get_source_color="color",
            get_target_color="color",
            get_width=lambda d: 5 if d.get("is_active") else 2,
            auto_highlight=True,
            pickable=True,
            width_scale=1,
            width_min_pixels=1,
        )

        # ── OSRM road polyline (PathLayer) ─────────────────────────────────────
        layers = [arc_layer, scatter_layer]
        if route_result:
            route_coords = route_result.get("route_coords")
            if route_coords:
                path_data = [{"path": [[lon, lat] for lat, lon in route_coords],
                               "color": [0, 207, 255]}]
                path_layer = pdk.Layer(
                    "PathLayer",
                    path_data,
                    get_path="path",
                    get_color="color",
                    width_scale=20,
                    width_min_pixels=3,
                    pickable=True,
                )
                layers.insert(0, path_layer)

        view = pdk.ViewState(**self.DHAKA_CENTER)
        deck = pdk.Deck(
            layers=layers,
            initial_view_state=view,
            tooltip={"text": "{name} [{status}]\n{label}"},
            map_style="mapbox://styles/mapbox/dark-v10",
        )
        st.pydeck_chart(deck)

    # ── Demand Hexagon + Column Maps ───────────────────────────────────────────

    def render_demand_columns(
        self,
        zone_demand: Dict[str, float],
    ) -> None:
        """
        3D extruded columns per hub — height ∝ demand value.
        Much faster than Folium CircleMarkers for large datasets.
        """
        if not PYDECK_AVAILABLE:
            self._not_available(); return

        max_val = max(zone_demand.values()) or 1.0
        col_data = []
        for name, (lat, lon) in DHAKA_HUBS.items():
            demand = zone_demand.get(name, 0)
            ratio  = demand / max_val
            elevation = int(ratio * 5000)
            r = int(255 * ratio)
            g = int(107 * (1 - ratio))
            col_data.append({
                "name":        name,
                "coordinates": [lon, lat],
                "elevation":   elevation,
                "color":       [r, 107, 53, 180],
                "demand":      int(demand),
            })

        col_layer = pdk.Layer(
            "ColumnLayer",
            col_data,
            get_position="coordinates",
            get_elevation="elevation",
            get_fill_color="color",
            elevation_scale=1,
            radius=400,
            pickable=True,
            extruded=True,
            coverage=0.9,
        )
        view = pdk.ViewState(**{**self.DHAKA_CENTER, "pitch": 55, "zoom": 11})
        deck = pdk.Deck(
            layers=[col_layer],
            initial_view_state=view,
            tooltip={"text": "{name}\nDemand: {demand}"},
            map_style="mapbox://styles/mapbox/dark-v10",
        )
        st.pydeck_chart(deck)


# ═══════════════════════════════════════════════════════════════════════════════
# ADVANCED GIS MODULE B ── ZONE ANALYZER (GeoPandas Point-in-Polygon)
# ═══════════════════════════════════════════════════════════════════════════════

# Approximate Dhaka zone polygons (bounding boxes as proxies for real GeoJSON).
# In production, replace these with proper shapefiles from OSM or BBS.
DHAKA_ZONE_POLYGONS: Dict[str, List[Tuple[float, float]]] = {
    "Gulshan":     [(23.760, 90.390), (23.760, 90.425), (23.810, 90.425), (23.810, 90.390)],
    "Dhanmondi":   [(23.730, 90.360), (23.730, 90.395), (23.760, 90.395), (23.760, 90.360)],
    "Mirpur":      [(23.800, 90.345), (23.800, 90.385), (23.845, 90.385), (23.845, 90.345)],
    "Uttara":      [(23.855, 90.360), (23.855, 90.400), (23.900, 90.400), (23.900, 90.360)],
    "Motijheel":   [(23.715, 90.410), (23.715, 90.430), (23.745, 90.430), (23.745, 90.410)],
    "Mohakhali":   [(23.765, 90.395), (23.765, 90.420), (23.795, 90.420), (23.795, 90.395)],
    "Badda":       [(23.760, 90.420), (23.760, 90.445), (23.800, 90.445), (23.800, 90.420)],
    "Rayer Bazar": [(23.735, 90.345), (23.735, 90.370), (23.765, 90.370), (23.765, 90.345)],
    "Wari":        [(23.710, 90.405), (23.710, 90.425), (23.730, 90.425), (23.730, 90.405)],
}


class ZoneAnalyzer:
    """
    Point-in-Polygon (PIP) zone assignment using GeoPandas + Shapely.

    Usage:
      za = ZoneAnalyzer()
      zone = za.get_zone(23.775, 90.408)   # → "Mohakhali"
      hub  = za.assign_nearest_hub(23.775, 90.408)  # → "Mohakhali"

    Falls back to nearest-centroid (Haversine) when GeoPandas is unavailable.
    """

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)
        self._gdf: Optional[Any] = None
        if GEOPANDAS_AVAILABLE:
            self._build_gdf()

    def _build_gdf(self) -> None:
        """Build a GeoDataFrame from the approximate zone polygons."""
        try:
            records = []
            for zone_name, coords in DHAKA_ZONE_POLYGONS.items():
                poly = Polygon([(lon, lat) for lat, lon in coords])
                records.append({"zone": zone_name, "geometry": poly})
            self._gdf = gpd.GeoDataFrame(records, geometry="geometry", crs="EPSG:4326")
            self.logger.info("ZoneAnalyzer: GeoPandas GDF built (%d zones)", len(records))
        except Exception as exc:
            self.logger.error("ZoneAnalyzer GDF build failed: %s", exc)
            self._gdf = None

    def get_zone(self, lat: float, lon: float) -> Optional[str]:
        """
        Return the zone name that contains the point (lat, lon).
        Uses Point-in-Polygon if GeoPandas is available; otherwise None.
        """
        if self._gdf is not None:
            try:
                pt = Point(lon, lat)
                hits = self._gdf[self._gdf.geometry.contains(pt)]
                if not hits.empty:
                    return hits.iloc[0]["zone"]
            except Exception as exc:
                self.logger.warning("PIP failed: %s", exc)
        return None

    def assign_nearest_hub(self, lat: float, lon: float) -> str:
        """
        Return the hub whose centroid is closest to (lat, lon).
        First tries PIP zone assignment; falls back to Haversine nearest-centroid.
        """
        zone = self.get_zone(lat, lon)
        if zone and zone in DHAKA_HUBS:
            return zone
        # Haversine fallback
        def haversine(p1, p2):
            R = 6371.0
            la1, lo1 = math.radians(p1[0]), math.radians(p1[1])
            la2, lo2 = math.radians(p2[0]), math.radians(p2[1])
            a = math.sin((la2-la1)/2)**2 + math.cos(la1)*math.cos(la2)*math.sin((lo2-lo1)/2)**2
            return R * 2 * math.asin(math.sqrt(a))
        return min(DHAKA_HUBS.keys(), key=lambda h: haversine(DHAKA_HUBS[h], (lat, lon)))

    def zone_summary(self) -> str:
        """Return a Markdown table of zones and their centroid hubs."""
        lines = ["| Zone | Center Hub | GDF Status |",
                 "|------|-----------|-----------|"]
        for z in DHAKA_ZONE_POLYGONS:
            center_lat = sum(c[0] for c in DHAKA_ZONE_POLYGONS[z]) / 4
            center_lon = sum(c[1] for c in DHAKA_ZONE_POLYGONS[z]) / 4
            hub = self.assign_nearest_hub(center_lat, center_lon)
            pip = "✅ PIP" if self._gdf is not None else "⚠️ Haversine"
            lines.append(f"| {z} | {hub} | {pip} |")
        return "\n".join(lines)



# ── Global CSS ────────────────────────────────────────────────────────────────

NEXUS_CSS = """
<style>
[data-testid="stAppViewContainer"] {
    background: linear-gradient(135deg,#0a0e1a 0%,#0d1224 60%,#080c18 100%);
    color: #e0e8ff;
}
[data-testid="stSidebar"] {
    background: linear-gradient(180deg,#0d1224 0%,#0a0e1a 100%);
    border-right: 1px solid #1e2a44;
}
h1,h2,h3 { color: #00ff88 !important; letter-spacing: .4px; }
h4,h5    { color: #7dd3fc !important; }
p, li, label, .stMarkdown { color: #c8d6f0 !important; }

[data-testid="metric-container"] {
    background: linear-gradient(135deg,#111827 0%,#1a2235 100%);
    border: 1px solid #1e3a5f; border-radius: 12px;
    padding: .9rem 1.1rem;
    box-shadow: 0 0 16px rgba(0,255,136,.05);
}
[data-testid="stMetricValue"]{ color: #00ff88 !important; font-size: 1.55rem !important; }

.stButton>button {
    background: linear-gradient(135deg,#1a3a5c,#0d2040) !important;
    color: #00ff88 !important;
    border: 1px solid #00ff88 !important;
    border-radius: 8px !important;
    font-weight: 600 !important;
    transition: all .2s ease;
}
.stButton>button:hover {
    background: linear-gradient(135deg,#00ff88,#00cc77) !important;
    color: #0a0e1a !important;
    box-shadow: 0 0 16px rgba(0,255,136,.4) !important;
}

[data-testid="stSelectbox"]>div>div,
[data-testid="stTextInput"]>div>div,
[data-testid="stNumberInput"]>div>div {
    background: #111827 !important;
    border: 1px solid #1e3a5f !important;
    color: #e0e8ff !important;
    border-radius: 8px !important;
}

[data-testid="stDataFrame"] {
    border: 1px solid #1e3a5f !important; border-radius: 10px !important;
}
thead tr th { background:#0d1e35!important; color:#00ff88!important; font-size:.8rem!important; text-transform:uppercase; }
tbody tr:nth-child(odd)  { background:#0d1422!important; }
tbody tr:nth-child(even) { background:#101828!important; }
tbody tr:hover           { background:#152032!important; }
td { color:#d0daf0!important; font-size:.85rem!important; }

.stAlert { border-radius: 10px !important; border-left-width: 4px !important; }
details { border:1px solid #1e3a5f!important; border-radius:10px!important; background:#0d1224!important; padding:.5rem!important; }
summary { color:#7dd3fc!important; font-weight:600!important; }
.stProgress>div>div { background:#00ff88!important; }
[data-testid="stTabs"] [data-baseweb="tab"] { color:#7dd3fc!important; }
[data-testid="stTabs"] [aria-selected="true"] { color:#00ff88!important; border-bottom:2px solid #00ff88!important; }

.nx-card {
    background: linear-gradient(135deg,#111827,#1a2235);
    border: 1px solid #1e3a5f; border-radius:12px;
    padding:1.1rem 1.3rem; margin-bottom:.7rem;
    box-shadow:0 4px 20px rgba(0,200,255,.04);
}
.nx-card h4 { color:#7dd3fc!important; margin-top:0; }
.nx-card p  { color:#b0bcd8!important; font-size:.87rem; line-height:1.6; }

.badge-critical { color:#ff3366; font-weight:700; }
.badge-urgent   { color:#ffbb00; font-weight:700; }
.badge-stable   { color:#00ff88; font-weight:700; }
.badge-monitor  { color:#7dd3fc; font-weight:700; }
.badge-overstock{ color:#c084fc; font-weight:700; }

.source-live    { color:#00ff88; font-size:.72rem; font-weight:600; }
.source-cached  { color:#ffbb00; font-size:.72rem; font-weight:600; }
.source-ref     { color:#ff6b35; font-size:.72rem; font-weight:600; }
.sb-metric { background:#111827;border:1px solid #1e3a5f;border-radius:8px;
             padding:.45rem .8rem;margin-bottom:.35rem;font-size:.8rem;color:#c8d6f0; }

::-webkit-scrollbar{width:6px;height:6px;}
::-webkit-scrollbar-track{background:#0a0e1a;}
::-webkit-scrollbar-thumb{background:#1e3a5f;border-radius:3px;}
::-webkit-scrollbar-thumb:hover{background:#00ff88;}

/* ── MOBILE RESPONSIVE ──────────────────────────────────────────────────── */
@media (max-width: 768px) {
    /* Sidebar collapses nicely on mobile */
    [data-testid="stSidebar"] { width: 100% !important; }

    /* Stack Streamlit columns vertically on mobile */
    [data-testid="column"] {
        min-width: 100% !important;
        flex: 1 1 100% !important;
    }

    /* Metrics: 2 per row on mobile */
    [data-testid="metric-container"] {
        min-width: 45% !important;
    }

    /* Reduce font sizes for headings */
    h1 { font-size: 1.4rem !important; }
    h2 { font-size: 1.2rem !important; }
    h3 { font-size: 1.05rem !important; }

    /* Tab labels smaller */
    [data-testid="stTabs"] [data-baseweb="tab"] {
        font-size: .72rem !important;
        padding: .4rem .5rem !important;
    }

    /* Cards full width */
    .nx-card { padding: .85rem .95rem !important; }

    /* Buttons full width on mobile */
    .stButton > button { width: 100% !important; }

    /* Tables: allow horizontal scroll */
    [data-testid="stDataFrame"] { overflow-x: auto !important; }

    /* Main content area: reduce side padding */
    .main .block-container {
        padding-left: .75rem !important;
        padding-right: .75rem !important;
        padding-top: .75rem !important;
    }
}

@media (max-width: 480px) {
    /* Extra small phones */
    [data-testid="metric-container"] { min-width: 100% !important; }
    h1 { font-size: 1.2rem !important; }
    [data-testid="stTabs"] [data-baseweb="tab"] {
        font-size: .65rem !important;
        padding: .35rem .4rem !important;
    }
}
</style>
"""

# ── Shared helpers ────────────────────────────────────────────────────────────

def _inject_css() -> None:
    st.markdown(NEXUS_CSS, unsafe_allow_html=True)

def _spark_bar(vals: List[float], color: str = "#00ff88", height: int = 40) -> str:
    if not vals: return ""
    mx   = max(vals) or 1
    bars = "".join(
        f'<div style="width:{max(100//len(vals),3)}px;height:{int(v/mx*height)}px;'
        f'background:{color};border-radius:2px 2px 0 0;display:inline-block;'
        f'margin:0 1px;vertical-align:bottom;opacity:.88;" title="{v:.1f}"></div>'
        for v in vals
    )
    return f'<div style="display:flex;align-items:flex-end;height:{height+4}px;">{bars}</div>'

def _score_badge_html(action: str) -> str:
    mp = {
        "CRITICAL_ORDER": ("🔴","badge-critical"),
        "URGENT_ORDER":   ("🟡","badge-urgent"),
        "MONITOR":        ("🔵","badge-monitor"),
        "STABLE":         ("🟢","badge-stable"),
        "OVERSTOCK":      ("🟣","badge-overstock"),
    }
    icon, cls = mp.get(action, ("⚪","badge-stable"))
    return f'<span class="{cls}">{icon} {action}</span>'

def _wx_icon(cond: str) -> str:
    c = cond.lower()
    if "rain"  in c: return "🌧️"
    if "cloud" in c: return "⛅"
    if "clear" in c or "sun" in c: return "☀️"
    if "storm" in c: return "⛈️"
    if "fog"   in c or "mist" in c: return "🌫️"
    return "🌡️"

def _source_badge(source: str) -> str:
    if "live" in source:   return f'<span class="source-live">● LIVE</span>'
    if "cache" in source:  return f'<span class="source-cached">● CACHED</span>'
    return f'<span class="source-ref">● REF</span>'


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK AUTH ── AUTHENTICATION & RBAC MANAGER
# ═══════════════════════════════════════════════════════════════════════════════

# Minimal login-page CSS injected once
_LOGIN_CSS = """
<style>
[data-testid="stAppViewContainer"] {
    background: #0a0e1a !important;
}
[data-testid="stSidebar"] { display: none !important; }

.logix-login-wrap {
    display: flex; flex-direction: column; align-items: center;
    justify-content: center; min-height: 88vh;
}
.logix-login-card {
    background: linear-gradient(145deg, #0d1224 0%, #111827 100%);
    border: 1px solid #1e3a5f;
    border-radius: 18px;
    padding: 2.8rem 3rem 2.2rem;
    width: 100%; max-width: 420px;
    box-shadow: 0 8px 40px rgba(0,255,136,0.08);
}
.logix-login-logo {
    font-size: 2.6rem; font-weight: 900; letter-spacing: 4px;
    color: #00ff88; text-align: center; margin-bottom: 0.2rem;
}
.logix-login-sub {
    color: #4a6fa5; font-size: .82rem; text-align: center;
    margin-bottom: 2rem; letter-spacing: .5px;
}
.logix-login-card input {
    background: #0d1224 !important;
    border: 1px solid #1e3a5f !important;
    color: #e0e8ff !important;
    border-radius: 8px !important;
}
/* Fix: use Streamlit's actual button class instead of [kind] attribute */
.logix-login-card .stButton > button {
    background: linear-gradient(90deg,#00ff88,#00cfff) !important;
    color: #0a0e1a !important; font-weight: 700 !important;
    border-radius: 8px !important; border: none !important;
    width: 100% !important; padding: .65rem !important;
}
.logix-login-error {
    background: rgba(255,51,102,0.12);
    border: 1px solid #ff3366;
    border-radius: 8px; padding: .75rem 1rem;
    color: #ff6b8a; font-size: .85rem; margin-top: .8rem;
    text-align: center;
}
.logix-login-hint {
    color: #2a4a6a; font-size: .74rem; text-align: center;
    margin-top: 1.2rem; line-height: 1.6;
}
/* Mobile responsiveness for login */
@media (max-width: 600px) {
    .logix-login-card {
        padding: 2rem 1.4rem 1.6rem;
        border-radius: 14px;
        max-width: 96vw;
    }
    .logix-login-logo { font-size: 2rem; }
}
</style>
"""


class AuthManager:
    """
    Authentication & Role-Based Access Control manager for LOGIX.

    Responsibilities:
    ─────────────────
    • Render a dark-themed login screen matching LOGIX's design language.
    • Validate credentials against the `users` SQLite table.
    • Persist auth context in st.session_state[_AUTH_KEY].
    • Provide role-checking helpers (is_admin, has_tab_access, etc.).
    • Supply the log_action() audit helper used throughout NexusUI.
    • Handle logout and session teardown.
    """

    def __init__(self, db: "NexusDatabase") -> None:
        self.db     = db
        self.logger = logging.getLogger(self.__class__.__name__)

    # ── Public helpers ─────────────────────────────────────────────────────────

    def is_authenticated(self) -> bool:
        """Return True if a valid auth context exists in session_state."""
        ctx = st.session_state.get(_AUTH_KEY, {})
        return bool(ctx.get("logged_in") and ctx.get("username"))

    def current_user(self) -> Dict[str, str]:
        """
        Return the current user context dict.
        Keys: username, name, role, logged_in.
        Returns an empty-ish dict when not authenticated.
        """
        return st.session_state.get(_AUTH_KEY, {
            "username": "guest", "name": "Guest", "role": "dispatcher", "logged_in": False
        })

    def current_role(self) -> str:
        return self.current_user().get("role", "dispatcher")

    def is_admin(self) -> bool:
        return self.current_role() == "admin"

    def has_tab(self, tab_index: int) -> bool:
        """Return True if the current role can view a given tab index."""
        allowed = ROLE_TAB_ACCESS.get(self.current_role(), [])
        return tab_index in allowed

    def allowed_tabs(self) -> List[str]:
        """Return the subset of ALL_TABS the current user may see."""
        allowed_indices = ROLE_TAB_ACCESS.get(self.current_role(), [])
        return [ALL_TABS[i] for i in sorted(allowed_indices)]

    def log_action(self, action_type: str, description: str) -> None:
        """
        Write an audit log entry for the currently authenticated user.
        Safe to call even if no user is logged in (records 'anonymous').
        """
        ctx = self.current_user()
        self.db.log_audit(
            username    = ctx.get("username", "anonymous"),
            role        = ctx.get("role",     "unknown"),
            action_type = action_type,
            description = description,
        )

    # ── Login screen ───────────────────────────────────────────────────────────

    def render_login(self) -> bool:
        """
        Render the full-screen login UI.
        Returns True immediately if the user is already authenticated.
        Writes auth context to st.session_state[_AUTH_KEY] on success.
        """
        if self.is_authenticated():
            return True

        # Inject login-page CSS (hides sidebar, applies dark card theme)
        st.markdown(_LOGIN_CSS, unsafe_allow_html=True)

        # Centre the card using columns
        _, col, _ = st.columns([1, 1.6, 1])
        with col:
            st.markdown(
                '<div class="logix-login-logo">LOGIX</div>'
                '<div class="logix-login-sub">Supply Chain Intelligence Platform</div>',
                unsafe_allow_html=True,
            )

            username = st.text_input(
                "Username", placeholder="Enter your username", key="login_user"
            )
            password = st.text_input(
                "Password", type="password", placeholder="Enter your password",
                key="login_pass"
            )

            login_clicked = st.button(
                "🔐 Sign In", type="primary", use_container_width=True, key="login_btn"
            )

            # ── Credential validation ─────────────────────────────────────────
            if login_clicked:
                if not username.strip() or not password.strip():
                    st.markdown(
                        '<div class="logix-login-error">⚠️ Please enter both username and password.</div>',
                        unsafe_allow_html=True,
                    )
                else:
                    user_row = self.db.get_user(username.strip().lower())
                    if user_row and NexusDatabase.verify_password(password, user_row["hashed_password"]):
                        # ── SUCCESS ──────────────────────────────────────────
                        st.session_state[_AUTH_KEY] = {
                            "logged_in": True,
                            "username":  user_row["username"],
                            "name":      user_row["name"],
                            "role":      user_row["role"],
                            "login_ts":  time.time(),
                        }
                        # Write audit entry
                        self.db.log_audit(
                            user_row["username"], user_row["role"],
                            "AUTH_LOGIN",
                            f"User '{user_row['name']}' logged in successfully.",
                        )
                        self.logger.info("Login: %s (%s)", user_row["username"], user_row["role"])
                        st.rerun()
                    else:
                        # ── FAILURE ───────────────────────────────────────────
                        self.logger.warning("Failed login attempt: username='%s'", username)
                        # Log failed attempt (no user row needed)
                        self.db.log_audit(
                            username.strip().lower(), "unknown",
                            "AUTH_FAILED",
                            f"Failed login attempt for username '{username.strip().lower()}'.",
                        )
                        st.markdown(
                            '<div class="logix-login-error">❌ Invalid username or password. Please try again.</div>',
                            unsafe_allow_html=True,
                        )

            st.markdown(
                '<div class="logix-login-hint">'
                "Demo accounts — change in production:<br>"
                "<b>admin</b> / Admin@1234 &nbsp;|&nbsp; "
                "<b>manager</b> / Manager@456 &nbsp;|&nbsp; "
                "<b>dispatcher</b> / Rider@789"
                "</div>",
                unsafe_allow_html=True,
            )

        return self.is_authenticated()

    def render_logout(self) -> None:
        """
        Render the profile badge + logout button inside the sidebar.
        Call this at the TOP of NexusUI._sidebar().
        """
        ctx  = self.current_user()
        role = ctx.get("role", "dispatcher")
        meta = ROLE_META.get(role, {"label": role.title(), "color": "#7dd3fc"})

        st.sidebar.markdown(
            f"<div style='background:rgba(0,255,136,0.06);border:1px solid #1e3a5f;"
            f"border-radius:10px;padding:.7rem 1rem;margin-bottom:.8rem;'>"
            f"<span style='font-size:1.1rem;'>👤</span> "
            f"<b style='color:#e0e8ff;'>{ctx.get('name','?')}</b><br>"
            f"<span style='font-size:.75rem;color:{meta['color']};font-weight:700;"
            f"letter-spacing:.5px;'>⬡ {meta['label'].upper()}</span>"
            f"&nbsp;<span style='font-size:.72rem;color:#4a6fa5;'>@{ctx.get('username','?')}</span>"
            f"</div>",
            unsafe_allow_html=True,
        )

        if st.sidebar.button("🚪 Logout", use_container_width=True, key="logout_btn"):
            # Audit the logout event before clearing state
            self.log_action("AUTH_LOGOUT", f"User '{ctx.get('name')}' logged out.")
            # Wipe auth context but keep other state intact
            st.session_state.pop(_AUTH_KEY, None)
            st.rerun()


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 7 ── PRESENTATION LAYER (NEXUS UI)
# ═══════════════════════════════════════════════════════════════════════════════

class NexusUI:
    """
    Full Streamlit 10-tab UI for LOGIX v7.2.
    Developer: Sourab Dey Soptom.

    RBAC-aware: render() checks AuthManager before drawing any content.
    Tab set is built dynamically from ROLE_TAB_ACCESS for the active session role.
    All destructive actions are gated behind is_admin() checks.
    Audit trail written via log_action() on key mutations.
    """

    def __init__(self, db: NexusDatabase, scraper: LiveDataScraper,
                 soptom: SoptomAlgorithm, dss: DSSEngine,
                 business: BusinessEngine, routing: RoutingEngine,
                 maps: MapRenderer,
                 pydeck: Optional[Any] = None,
                 zones:  Optional[Any] = None,
                 auth:   Optional[Any] = None) -> None:
        self.db       = db
        self.scraper  = scraper
        self.soptom   = soptom
        self.dss      = dss
        self.business = business
        self.routing  = routing
        self.maps     = maps
        self.pydeck   = pydeck   # PyDeckRenderer — may be None
        self.zones    = zones    # ZoneAnalyzer   — may be None
        self.auth     = auth     # AuthManager    — may be None
        self.logger   = logging.getLogger(self.__class__.__name__)

    # ── Audit shortcut ────────────────────────────────────────────────────────

    def log_action(self, action_type: str, description: str) -> None:
        """
        Convenience wrapper — writes an audit_log row for the active session user.
        Falls back silently if AuthManager is not wired up.
        """
        if self.auth:
            self.auth.log_action(action_type, description)
        else:
            self.db.log_audit("system", "system", action_type, description)

    # ── Entry point ───────────────────────────────────────────────────────────

    def render(self) -> None:
        _inject_css()

        # ── STEP 1: Authentication gate ────────────────────────────────────────
        # If AuthManager is present, enforce login before any app content.
        if self.auth and not self.auth.render_login():
            # render_login() already drew the login form — stop here.
            return

        # ── STEP 2: Sidebar (includes profile badge + logout button) ──────────
        self._sidebar()

        # ── STEP 3: Role-based dynamic tab construction ───────────────────────
        #
        # ALL_TABS is the canonical ordered list of all 10 tab labels.
        # ROLE_TAB_ACCESS maps each role → list of allowed tab indices.
        # We build `visible_tabs` (labels) and `index_map` (label → original index)
        # so each tab method (_t0_, _t1_, …) is dispatched by its original index
        # regardless of how many tabs are visible to the current role.
        #
        current_role = self.auth.current_role() if self.auth else "admin"
        allowed_indices = ROLE_TAB_ACCESS.get(current_role, list(range(len(ALL_TABS))))

        visible_labels = [ALL_TABS[i] for i in sorted(allowed_indices)]
        index_map: Dict[str, int] = {ALL_TABS[i]: i for i in sorted(allowed_indices)}

        tabs = st.tabs(visible_labels)

        # ── STEP 4: Preload shared data ────────────────────────────────────────
        prices  = self.scraper.fetch_chaldal_prices()
        weather = self.scraper.fetch_weather_data()
        inv     = self.db.get_inventory()
        self.db.update_inventory_from_prices(prices)
        event   = st.session_state.get("market_event", "Normal Day")
        fcs     = st.session_state.get("forecasts", {})

        # ── STEP 5: Tab dispatch ───────────────────────────────────────────────
        # Map each visible tab position to the correct _tN_ method.
        _TAB_METHODS = {
            0: lambda: self._t0_command(prices, weather, inv, event, fcs),
            1: lambda: self._t1_inventory(inv, prices, event),
            2: lambda: self._t2_ai(inv, prices, weather, event, fcs),
            3: lambda: self._t3_dss(inv, prices, fcs),
            4: lambda: self._t4_map(inv, prices, fcs),
            5: lambda: self._t5_logistics(inv, prices),
            6: lambda: self._t6_finance(inv, prices),
            7: lambda: self._t7_alerts(),
            8: lambda: self._t8_ai_logs(),
            9: lambda: self._t9_settings(inv, prices, fcs),
        }

        for tab_widget, label in zip(tabs, visible_labels):
            original_idx = index_map[label]
            with tab_widget:
                method = _TAB_METHODS.get(original_idx)
                if method:
                    method()

    # ── Sidebar ───────────────────────────────────────────────────────────────

    def _sidebar(self) -> None:
        with st.sidebar:
            st.markdown(
                "<h2 style='color:#00ff88;letter-spacing:1px;'>LOGIX</h2>"
                "<p style='color:#7dd3fc;font-size:.78rem;margin-top:0;'>developed by Sourab Dey Soptom </p>",
                unsafe_allow_html=True,
            )

            # ── Profile badge + Logout (RBAC) ─────────────────────────────────
            if self.auth:
                self.auth.render_logout()

            # Data source badge
            src_label = self.scraper.get_data_source_label()
            st.markdown(f"**Data:** {src_label}")
            st.divider()

            events    = list(EVENT_DEMAND_FACTORS.keys())
            chosen    = st.selectbox(
                "📅 Market Event", events,
                index=events.index(st.session_state.get("market_event","Normal Day")),
                key="sb_event",
            )
            st.session_state["market_event"] = chosen

            st.divider()
            ac = self.db.get_alert_count()
            c, w = ac.get("critical",0), ac.get("warning",0)
            if c > 0:   st.error(f"🚨 {c} Critical Alert{'s' if c>1 else ''}")
            elif w > 0: st.warning(f"⚠️ {w} Warning{'s' if w>1 else ''}")
            else:       st.success("✅ All Systems Normal")

            inv = self.db.get_inventory()
            ls  = sum(1 for i in inv if i.get("current_stock",99) < i.get("reorder_point",20))
            st.markdown(
                f'<div class="sb-metric">📦 SKUs: <b>{len(inv)}</b></div>'
                f'<div class="sb-metric">⚠️ Low-stock: <b style="color:#ffbb00">{ls}</b></div>'
                f'<div class="sb-metric">🤖 AI: <b style="color:#7dd3fc">{self.soptom.get_model_name()[:20]}</b></div>'
                f'<div class="sb-metric">🔌 LLM: <b style="color:{"#00ff88" if self.soptom.is_llm_active() else "#ff3366"}">'
                f'{"Active" if self.soptom.is_llm_active() else "Rule-based"}</b></div>',
                unsafe_allow_html=True,
            )
            st.divider()

            if st.button("🔄 Refresh All Data", use_container_width=True):
                self.scraper.force_refresh()
                for k in [k for k in st.session_state if k.startswith(("market_brief_","deep_result_","proc_plan","dss_","forecasts"))]:
                    del st.session_state[k]
                st.rerun()

            if st.button("🤖 Run Auto-Alerts", use_container_width=True):
                w2 = self.scraper.fetch_weather_data()
                p2 = self.scraper.fetch_chaldal_prices()
                i2 = self.db.get_inventory()
                n  = self.business.auto_generate_alerts(i2, p2, w2)
                st.success(f"Generated {n} alert(s)")
                st.rerun()

            st.caption(f"v{APP_VERSION}  |  DB: {Path(DB_PATH).name}")

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 0 — COMMAND CENTRE
    # ═════════════════════════════════════════════════════════════════════════

    def _t0_command(self, prices: Dict, weather: Dict, inv: List[Dict],
                    event: str, fcs: Dict) -> None:
        st.markdown("## 🏠 Command Centre")
        src_label = self.scraper.get_data_source_label()
        st.caption(f"Data: {src_label}  |  Cache TTL: {SCRAPE_TTL}s  |  Event: **{event}**")

        # ── KPI row ─────────────────────────────────────────────────────────
        total_stk = sum(i.get("current_stock",0) for i in inv)
        low_cnt   = sum(1 for i in inv if i.get("current_stock",99) < i.get("reorder_point",20))
        exp_warn  = sum(1 for i in inv if i.get("expiry_days",99) <= 5)
        inv_val   = sum(i.get("current_stock",0)*i.get("unit_cost",0) for i in inv)
        stats     = self.db.get_order_stats()
        revenue   = stats.get("revenue") or 0

        # ── KPI row: 3+3 split so mobile renders 2 neat rows instead of overflow ──
        r1c1, r1c2, r1c3 = st.columns(3)
        r1c1.metric("📦 Total Stock",    f"{total_stk:,}")
        r1c2.metric("⚠️ Low Stock",      low_cnt,   delta=None, delta_color="inverse")
        r1c3.metric("🕐 Expiry Alerts",  exp_warn,  delta=None, delta_color="inverse")
        r2c1, r2c2, r2c3 = st.columns(3)
        r2c1.metric("💰 Revenue (৳)",    f"{revenue:,.0f}")
        r2c2.metric("📋 Total Orders",   stats.get("total",0))
        r2c3.metric("✅ Delivered",       stats.get("delivered",0))

        st.divider()

        # ── Weather + AI brief ───────────────────────────────────────────────
        col_w, col_a = st.columns([1,2])
        with col_w:
            st.markdown("### 🌤️ Dhaka Weather")
            icon = _wx_icon(weather.get("condition",""))
            cond = weather.get("condition","?")
            wsrc = "🟢 Live" if weather.get("source") == "live" else "🔴 Default"
            st.markdown(
                f'<div class="nx-card">'
                f'<h4>{icon} {cond} <span style="font-size:.7rem;color:#7dd3fc;">{wsrc}</span></h4>'
                f'<p>🌡️ {weather.get("temp_c","?")}°C (feels {weather.get("feels_like","?")}°C)<br>'
                f'💧 Humidity: {weather.get("humidity","?")}%<br>'
                f'🌬️ Wind: {weather.get("wind_kph","?")} km/h<br>'
                f'🌧️ Rain chance: {weather.get("rain_chance","?")}%<br>'
                f'☀️ UV Index: {weather.get("uv_index","?")}</p></div>',
                unsafe_allow_html=True,
            )
            factors = EVENT_DEMAND_FACTORS.get(event, {})
            hot  = [SKUS[s][0] for s, f in factors.items() if f > 1.4]
            cold = [SKUS[s][0] for s, f in factors.items() if f < 0.7]
            if hot:  st.markdown(f"🔥 **High demand:** {', '.join(hot[:4])}")
            if cold: st.markdown(f"❄️ **Low demand:** {', '.join(cold[:3])}")

        with col_a:
            st.markdown("### 🤖 Soptom AI — Market Intelligence")
            ai_key = f"market_brief_{event}_{weather.get('temp_c',30)}"
            if ai_key not in st.session_state:
                with st.spinner("Analysing market context…"):
                    brief = self.soptom.analyze_market_context(event, prices, weather)
                    self.db.log_ai_event("market_analysis","all",{"event":event},brief,self.soptom.get_model_name())
                    st.session_state[ai_key] = brief
            st.markdown(
                f'<div class="nx-card"><p>{st.session_state[ai_key]}</p></div>',
                unsafe_allow_html=True,
            )
            if st.button("🔁 Refresh AI Brief", key="ref_brief"):
                if ai_key in st.session_state: del st.session_state[ai_key]
                st.rerun()

        st.divider()

        # ── Live price ticker ────────────────────────────────────────────────
        st.markdown("### 💹 Live Chaldal Price Ticker")
        price_cols = st.columns(len(prices))
        for i, (sid, info) in enumerate(prices.items()):
            p    = info.get("price",0) or 0
            pp   = info.get("prev_price",p) or p
            name = info.get("name",sid)
            dt   = p - pp
            col  = "#00ff88" if dt <= 0 else "#ff3366"
            arr  = "▲" if dt > 0 else ("▼" if dt < 0 else "—")
            src  = info.get("data_source","?")
            src_c= "#00ff88" if "live" in src else ("#ffbb00" if "cache" in src else "#ff6b35")
            with price_cols[i]:
                st.markdown(
                    f'<div style="background:#111827;border:1px solid #1e3a5f;border-radius:8px;'
                    f'padding:.5rem;text-align:center;">'
                    f'<div style="font-size:.72rem;color:#7dd3fc;">{name[:12]}</div>'
                    f'<div style="font-size:1.05rem;font-weight:700;color:#e0e8ff;">৳{p}</div>'
                    f'<div style="font-size:.72rem;color:{col};">{arr} ৳{abs(dt):.0f}</div>'
                    f'<div style="font-size:.68rem;color:{src_c};">● {src[:8]}</div>'
                    f'</div>',
                    unsafe_allow_html=True,
                )

        st.divider()

        # ── Inventory Health Intelligence Dashboard ───────────────────────────
        st.markdown("### 📊 Inventory Health Intelligence")
        import json as _json, datetime as _dt

        _now_ts = _dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        # ── Per-SKU rich metrics ──────────────────────────────────────────────
        _rows = []
        _cat_counts = {"Healthy": 0, "Watch": 0, "Critical": 0, "Overstock": 0}
        for _item in inv:
            _sid  = _item.get("sku_id", "")
            _name = _item.get("name", _sid)
            _cat  = _item.get("category", "")
            _stk  = _item.get("current_stock", 0)
            _rop  = _item.get("reorder_point", 20)
            _eoq  = max(_item.get("eoq", 50), 1)
            _exp  = _item.get("expiry_days", 999)
            _cost = _item.get("unit_cost", 0) or 0
            _sell = (prices.get(_sid, {}).get("price") or
                     _item.get("selling_price") or
                     _cost * 1.15 or 1)
            _sell = float(_sell) if _sell else _cost * 1.15 or 1

            _ratio      = _stk / _eoq
            _ss = (0   if _stk == 0 else
                   15  if _stk < _rop * 0.5 else
                   35  if _stk < _rop else
                   85  if _ratio <= 1.0 else
                   100 if _ratio <= 2.0 else 60)
            _es = (0   if _exp <= 1 else
                   20  if _exp <= 3 else
                   50  if _exp <= 7 else
                   80  if _exp <= 30 else 100)
            _ms = min(max((_sell - _cost) / _sell * 200, 0), 100) if _sell > 0 else 50
            _hs = round(_ss * 0.50 + _es * 0.30 + _ms * 0.20)
            _mg = round((_sell - _cost) / max(_sell, 1) * 100, 1)

            if   _stk > _eoq * 2.0: _lbl = "Overstock"; _cat_counts["Overstock"]  += 1
            elif _hs >= 70:          _lbl = "Healthy";   _cat_counts["Healthy"]    += 1
            elif _hs >= 40:          _lbl = "Watch";     _cat_counts["Watch"]      += 1
            else:                    _lbl = "Critical";  _cat_counts["Critical"]   += 1

            _rows.append({
                "name": _name, "cat": _cat, "stk": _stk, "rop": _rop,
                "eoq": _eoq, "exp": min(_exp, 90), "cost": _cost,
                "sell": round(_sell, 1), "margin": _mg, "health": _hs,
                "label": _lbl, "urgency": 0 if _stk >= _rop else round(min((_rop - _stk) / max(_rop, 1) * 100, 100)),
                "ss": _ss, "es": _es, "ms": round(_ms, 1),
                "ratio": round(_ratio, 2),
                "half_rop": round(_rop * 0.5),
                "ov_thresh": _eoq * 2,
                "fill_pct": round(_ratio * 100, 1),
                "gap": _rop - _stk,
                "order_qty": max(0, _eoq - _stk),
                "days_cover": round(_stk / max(_rop / 7.0, 0.5), 1),
            })

        # ── Aggregate KPIs ────────────────────────────────────────────────────
        _avg_h      = round(sum(r["health"] for r in _rows) / max(len(_rows), 1))
        _need_order = sum(1 for r in _rows if r["stk"] < r["rop"])
        _exp_urgent = sum(1 for r in _rows if r["exp"] <= 3)

        _kc = st.columns(6)
        _kc[0].metric("🏥 Portfolio Health",  f"{_avg_h}/100")
        _kc[1].metric("🔴 Critical",  _cat_counts["Critical"],  delta_color="inverse")
        _kc[2].metric("🟡 Watch",     _cat_counts["Watch"],     delta_color="inverse")
        _kc[3].metric("🟢 Healthy",   _cat_counts["Healthy"])
        _kc[4].metric("⏰ Expire ≤3d", _exp_urgent,             delta_color="inverse")
        _kc[5].metric("📦 Need Order", _need_order,             delta_color="inverse")

        # ── Color helpers (Python-side, safe strings) ─────────────────────────
        def _hcol(r):
            return ("#ff3366" if r["label"] == "Critical"  else
                    "#ffbb00" if r["label"] == "Watch"     else
                    "#a855f7" if r["label"] == "Overstock" else "#00ff88")

        # ══════════════════════════════════════════════════════════════════════
        # IFRAME 1 — Stock Level Intelligence (line chart dashboard)
        # ══════════════════════════════════════════════════════════════════════
        _names   = [r["name"]      for r in _rows]
        _stks    = [r["stk"]       for r in _rows]
        _rops    = [r["rop"]       for r in _rows]
        _eoqs    = [r["eoq"]       for r in _rows]
        _hrops   = [r["half_rop"]  for r in _rows]
        _ovts    = [r["ov_thresh"] for r in _rows]
        _fills   = [r["fill_pct"]  for r in _rows]
        _gaps    = [r["gap"]       for r in _rows]
        _ordqs   = [r["order_qty"] for r in _rows]
        _dcovs   = [r["days_cover"]for r in _rows]
        _zones   = [r["label"]     for r in _rows]
        _ptcols  = [_hcol(r)       for r in _rows]
        _catsh   = [r["cat"][:8]   for r in _rows]
        _healths = [r["health"]    for r in _rows]
        _margins = [r["margin"]    for r in _rows]
        _urgents = [r["urgency"]   for r in _rows]

        _avg_fill = round(sum(_fills) / max(len(_fills), 1), 1)
        _total_ord = sum(_ordqs)

        # Tile counts
        _crit_n  = _cat_counts["Critical"]
        _low_n   = sum(1 for r in _rows if r["stk"] < r["rop"] and r["label"] != "Critical")
        _hlth_n  = _cat_counts["Healthy"]
        _ov_n    = _cat_counts["Overstock"]

        _i1_data = {
            "ts": _now_ts,
            "names": _names, "stks": _stks, "rops": _rops, "eoqs": _eoqs,
            "hrops": _hrops, "ovts": _ovts, "fills": _fills, "gaps": _gaps,
            "ordqs": _ordqs, "dcovs": _dcovs, "zones": _zones,
            "ptcols": _ptcols, "catsh": _catsh, "healths": _healths,
            "critN": _crit_n, "lowN": _low_n, "hlthN": _hlth_n, "ovN": _ov_n,
            "avgFill": _avg_fill, "totalOrd": _total_ord,
        }
        _i1_json = _json.dumps(_i1_data)

        _iframe1 = """<!DOCTYPE html><html><head>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0a0e1a;color:#e0e8ff;font-family:'Segoe UI',monospace,sans-serif;padding:14px}
.panel{background:linear-gradient(135deg,#0d1224,#111827);border:1px solid #1e3a5f;
  border-radius:12px;padding:14px;position:relative;overflow:hidden;margin-bottom:14px}
.panel::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;
  background:linear-gradient(90deg,#00ff88,#00cfff,#a855f7)}
.pt{font-size:.72rem;font-weight:700;color:#7dd3fc;letter-spacing:.7px;
    text-transform:uppercase;margin-bottom:8px}
.sub{font-size:.60rem;color:#94a3b8;margin-bottom:10px}
.tiles{display:grid;grid-template-columns:repeat(6,1fr);gap:8px;margin-bottom:12px}
.tile{background:#0a0e1a;border:1px solid #1e3a5f;border-radius:8px;
      padding:8px;text-align:center}
.tv{font-size:1.3rem;font-weight:800;line-height:1}
.tl{font-size:.58rem;color:#94a3b8;margin-top:3px}
.badges{display:grid;grid-template-columns:repeat(5,1fr);gap:8px;margin-top:12px}
.badge{background:#0a0e1a;border-left:3px solid #1e3a5f;border-radius:8px;
       padding:8px;font-size:.60rem}
.bn{font-size:.64rem;color:#7dd3fc;font-weight:700;margin-bottom:3px;
    white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.bz{font-size:.60rem;font-weight:800;margin-bottom:4px}
.br{display:flex;justify-content:space-between;color:#94a3b8;margin-top:1px}
.bv{color:#cbd5e1;font-weight:600}
.legend{display:flex;gap:14px;flex-wrap:wrap;margin-bottom:8px}
.lp{display:inline-flex;align-items:center;gap:5px;font-size:.62rem;font-weight:700;
    padding:2px 8px;border-radius:20px;border:1px solid}
</style></head><body>
<div id="root"></div>
<script>
const D = """ + _i1_json + """;
const GC='rgba(30,58,95,0.6)',LC='#7dd3fc',TC='#94a3b8';
Chart.defaults.color=TC;
Chart.defaults.font.family="'Segoe UI',monospace";
Chart.defaults.font.size=11;

function zCol(z){
  return z==='Critical'?'#ff3366':z==='Watch'?'#ffbb00':z==='Overstock'?'#a855f7':'#00ff88';
}
function zBg(z){
  return z==='Critical'?'rgba(255,51,102,.10)':z==='Watch'?'rgba(255,187,0,.07)':
         z==='Overstock'?'rgba(168,85,247,.08)':'rgba(0,255,136,.05)';
}

const root = document.getElementById('root');

// ── Tiles ─────────────────────────────────────────────────────────────
const tileData = [
  {v:D.critN,  l:'🔴 Critical',      c:'#ff3366'},
  {v:D.lowN,   l:'🟡 Below ROP',     c:'#ffbb00'},
  {v:D.hlthN,  l:'🟢 Healthy',       c:'#00ff88'},
  {v:D.ovN,    l:'🟣 Overstock',     c:'#a855f7'},
  {v:D.avgFill+'%',l:'📊 Avg Fill',  c:'#00cfff'},
  {v:D.totalOrd,   l:'📦 Units Needed',c:'#f97316'},
];
let tilesHTML = '<div class="tiles">';
tileData.forEach(t=>{
  tilesHTML += '<div class="tile"><div class="tv" style="color:'+t.c+'">'+t.v+'</div>'
             + '<div class="tl">'+t.l+'</div></div>';
});
tilesHTML += '</div>';

// ── Legend ─────────────────────────────────────────────────────────────
const legHTML = '<div class="legend">'
  +'<span class="lp" style="background:rgba(255,51,102,.18);border-color:#ff3366;color:#ff3366;">🔴 Critical &lt;½ROP</span>'
  +'<span class="lp" style="background:rgba(255,187,0,.14);border-color:#ffbb00;color:#ffbb00;">🟡 Low &lt;ROP</span>'
  +'<span class="lp" style="background:rgba(0,255,136,.12);border-color:#00ff88;color:#00ff88;">🟢 Healthy</span>'
  +'<span class="lp" style="background:rgba(168,85,247,.14);border-color:#a855f7;color:#a855f7;">🟣 Overstock &gt;2×EOQ</span>'
  +'<span style="font-size:.62rem;color:#475569;margin-left:auto">🕐 '+D.ts+'</span>'
  +'</div>';

// ── Zone band plugin ───────────────────────────────────────────────────
const zoneBands = {
  id:'zb',
  beforeDraw(chart){
    const {ctx,chartArea:{left,right,top,bottom},scales:{x,y}} = chart;
    if(!x||!y) return;
    const w=(right-left)/D.names.length;
    ctx.save();
    D.zones.forEach((z,i)=>{
      const cx=x.getPixelForValue(i);
      ctx.fillStyle=zBg(z);
      ctx.fillRect(cx-w/2,top,w,bottom-top);
    });
    ctx.restore();
  }
};

// ── Main stock line chart ──────────────────────────────────────────────
const c1 = document.createElement('div');
c1.className='panel';
c1.innerHTML='<div class="pt">📦 STOCK LEVEL INTELLIGENCE · Current vs ROP vs EOQ vs Thresholds</div>'
 +'<div class="sub">5 reference lines · Zone background per SKU · Per-point colour by health zone</div>'
 +legHTML+tilesHTML
 +'<div style="position:relative;height:320px"><canvas id="cStock"></canvas></div>'
 +'<div class="badges" id="badges"></div>'
 +'<div style="border-top:1px solid #1e3a5f;padding-top:12px;margin-top:14px">'
 +'<div class="pt" style="margin-bottom:8px">📊 STOCK FILL RATE · % of EOQ · Target 50–150%</div>'
 +'<div style="position:relative;height:110px"><canvas id="cFill"></canvas></div></div>'
 +'<div style="border-top:1px solid #1e3a5f;padding-top:12px;margin-top:14px">'
 +'<div class="pt" style="margin-bottom:8px">⚡ GAP TO REORDER POINT · + = Units Needed · − = Buffer Above ROP</div>'
 +'<div style="position:relative;height:110px"><canvas id="cGap"></canvas></div></div>';
root.appendChild(c1);

// Stock chart
new Chart(document.getElementById('cStock'),{
  type:'line', plugins:[zoneBands],
  data:{
    labels:D.names,
    datasets:[
      {label:'Current Stock',data:D.stks,borderColor:'#00cfff',borderWidth:2.5,
       tension:.38,fill:false,pointBackgroundColor:D.ptcols,pointBorderColor:D.ptcols,
       pointRadius:7,pointHoverRadius:10,pointBorderWidth:2,animation:false},
      {label:'Reorder Point',data:D.rops,borderColor:'#ffbb00',borderWidth:1.8,
       borderDash:[6,4],tension:.25,fill:false,pointRadius:4,pointHoverRadius:7,
       pointBackgroundColor:'#ffbb00',animation:false},
      {label:'EOQ Target',data:D.eoqs,borderColor:'#00ff88',borderWidth:1.8,
       borderDash:[8,5],tension:.25,fill:false,pointRadius:4,pointHoverRadius:7,
       pointBackgroundColor:'#00ff88',animation:false},
      {label:'2×EOQ Overstock',data:D.ovts,borderColor:'#a855f7',borderWidth:1.4,
       borderDash:[3,6],tension:.25,fill:false,pointRadius:3,animation:false},
      {label:'½ ROP Critical',data:D.hrops,borderColor:'rgba(255,51,102,.55)',borderWidth:1.2,
       borderDash:[2,8],tension:.25,fill:false,pointRadius:2,animation:false},
    ]
  },
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{
      legend:{labels:{color:LC,boxWidth:14,font:{size:10},usePointStyle:true}},
      tooltip:{
        backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',padding:11,
        callbacks:{
          title:ctx=>'📦 '+ctx[0].label,
          afterBody:ctx=>{
            const i=ctx[0].dataIndex;
            return['',
              '  Zone       : '+D.zones[i],
              '  Stock      : '+D.stks[i]+' units',
              '  ROP        : '+D.rops[i]+'  (gap: '+(D.gaps[i]>0?'+':'')+D.gaps[i]+')',
              '  EOQ        : '+D.eoqs[i],
              '  Fill Rate  : '+D.fills[i]+'% of EOQ',
              '  Days Cover : ~'+D.dcovs[i]+' days',
              '  Order Qty  : '+D.ordqs[i]+' units to reach EOQ',
            ];
          }
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:ctx=>zCol(D.zones[ctx.index]||'Healthy'),maxRotation:32,font:{size:10,weight:'600'}}},
      y:{grid:{color:GC},ticks:{color:TC},beginAtZero:true,title:{display:true,text:'Units',color:LC}}
    }
  }
});

// Fill rate chart
const frBand={id:'frb',beforeDraw(chart){
  const {ctx,chartArea:{left,right,top,bottom},scales:{y}}=chart;
  if(!y) return;
  const y50=y.getPixelForValue(50),y150=y.getPixelForValue(150),y100=y.getPixelForValue(100);
  ctx.save();
  ctx.fillStyle='rgba(0,255,136,.07)';
  ctx.fillRect(left,Math.min(y50,y150),right-left,Math.abs(y50-y150));
  ctx.strokeStyle='rgba(0,207,255,.35)';ctx.lineWidth=1;ctx.setLineDash([5,5]);
  ctx.beginPath();ctx.moveTo(left,y100);ctx.lineTo(right,y100);ctx.stroke();
  ctx.restore();
}};
new Chart(document.getElementById('cFill'),{
  type:'line',plugins:[frBand],
  data:{labels:D.names,datasets:[{
    label:'Fill Rate %',data:D.fills,borderColor:'#00cfff',borderWidth:2,
    tension:.38,fill:true,backgroundColor:'rgba(0,207,255,.06)',
    pointBackgroundColor:D.ptcols,pointBorderColor:D.ptcols,pointRadius:5,
    pointHoverRadius:8,animation:false
  }]},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:LC,boxWidth:12}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',
        callbacks:{title:ctx=>ctx[0].label,
          label:ctx=>'  Fill Rate: '+ctx.raw+'%  (target 50–150%)',
          afterLabel:ctx=>'  EOQ: '+D.eoqs[ctx.dataIndex]+'u  Stock: '+D.stks[ctx.dataIndex]+'u'
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC,font:{size:9},maxRotation:30}},
      y:{grid:{color:GC},ticks:{color:TC},beginAtZero:true,title:{display:true,text:'% of EOQ',color:LC}}
    }
  }
});

// Gap chart
const gCols=D.gaps.map(g=>g>0?'#ff3366':'#00ff88');
new Chart(document.getElementById('cGap'),{
  type:'line',
  data:{labels:D.names,datasets:[
    {label:'Gap to ROP',data:D.gaps,borderColor:'#7dd3fc',borderWidth:2,tension:.35,
     fill:false,pointBackgroundColor:gCols,pointBorderColor:gCols,pointRadius:5,
     pointHoverRadius:8,animation:false},
    {label:'Zero',data:D.names.map(()=>0),borderColor:'rgba(255,255,255,.15)',
     borderDash:[4,4],borderWidth:1,pointRadius:0,fill:false}
  ]},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:LC,boxWidth:12}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',
        callbacks:{title:ctx=>ctx[0].label,
          label:ctx=>{
            if(ctx.datasetIndex===1) return null;
            const g=ctx.raw;
            return g>0?'  ⚠️ Below ROP by '+g+' units':'  ✅ Above ROP by '+Math.abs(g)+' units';
          },
          afterLabel:ctx=>{
            if(ctx.datasetIndex===1) return null;
            const i=ctx.dataIndex;
            return '  Order to EOQ: '+D.ordqs[i]+'u  |  ~'+D.dcovs[i]+'d cover';
          }
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC,font:{size:9},maxRotation:30}},
      y:{grid:{color:GC},ticks:{color:TC},title:{display:true,text:'Gap (+ need, − buffer)',color:LC}}
    }
  }
});

// Badge strip
const badgeEl=document.getElementById('badges');
D.names.forEach((n,i)=>{
  const z=D.zones[i],col=zCol(z),bg=zBg(z);
  const zi=z==='Critical'?'🔴':z==='Watch'?'🟡':z==='Overstock'?'🟣':'🟢';
  badgeEl.innerHTML+='<div class="badge" style="background:'+bg+';border-left-color:'+col+';">'
    +'<div class="bn">'+n+'</div>'
    +'<div class="bz" style="color:'+col+'">'+zi+' '+z+'</div>'
    +'<div class="br"><span>Stock</span><span class="bv">'+D.stks[i]+'</span></div>'
    +'<div class="br"><span>ROP</span><span class="bv">'+D.rops[i]+'</span></div>'
    +'<div class="br"><span>EOQ</span><span class="bv">'+D.eoqs[i]+'</span></div>'
    +'<div class="br"><span>Fill</span><span class="bv" style="color:'+col+'">'+D.fills[i]+'%</span></div>'
    +'<div class="br"><span>Cover</span><span class="bv">~'+D.dcovs[i]+'d</span></div>'
    +'<div class="br"><span>Order</span><span class="bv" style="color:'+(D.ordqs[i]>0?'#f97316':'#00ff88')+'">'+(D.ordqs[i]===0?'—':D.ordqs[i]+' u')+'</span></div>'
    +'</div>';
});
</script></body></html>"""

        components.html(_iframe1, height=1720, scrolling=False)

        # ══════════════════════════════════════════════════════════════════════
        # IFRAME 2 — Radar · Donut · Health-vs-Margin · Urgency · Expiry · ABC
        # ══════════════════════════════════════════════════════════════════════

        # Top-6 SKUs for radar (by health score)
        _top6  = sorted(_rows, key=lambda r: -r["health"])[:6]
        _r_names = [r["name"][:11]  for r in _top6]
        _r_ss    = [r["ss"]         for r in _top6]
        _r_es    = [r["es"]         for r in _top6]
        _r_ms    = [round(r["ms"],1)for r in _top6]
        _r_ord   = [100-r["urgency"]for r in _top6]
        _r_ratio = [min(int(r["ratio"]*50),100) for r in _top6]
        _r_cols  = [_hcol(r)        for r in _top6]

        # Donut
        _d_labels = list(_cat_counts.keys())
        _d_vals   = list(_cat_counts.values())
        _d_total  = sum(_d_vals)

        # Health vs Margin scatter (all SKUs)
        _hm_names = [r["name"][:10]         for r in _rows]
        _hm_x     = [r["margin"]            for r in _rows]
        _hm_y     = [r["health"]            for r in _rows]
        _hm_r     = [max(r["stk"]//8, 4)   for r in _rows]
        _hm_cols  = [_hcol(r)               for r in _rows]

        # Margin line (sorted low→high)
        _mr_s    = sorted(_rows, key=lambda r: r["margin"])
        _mr_names= [r["name"][:11]  for r in _mr_s]
        _mr_vals = [r["margin"]     for r in _mr_s]
        _mr_sells= [r["sell"]       for r in _mr_s]
        _mr_costs= [r["cost"]       for r in _mr_s]
        _mr_cols = [_hcol(r)        for r in _mr_s]

        # ABC classification (by margin × stock value)
        _abc_s  = sorted(_rows, key=lambda r: -(r["margin"] * r["stk"]))
        _a_cut  = max(1, len(_abc_s) // 5)
        _b_cut  = max(2, len(_abc_s) // 2)
        _a_items= ", ".join(r["name"].split()[0] for r in _abc_s[:_a_cut])
        _b_items= ", ".join(r["name"].split()[0] for r in _abc_s[_a_cut:_b_cut])
        _c_items= ", ".join(r["name"].split()[0] for r in _abc_s[_b_cut:])

        # Expiry (sorted urgent first)
        _ex_s   = sorted(_rows, key=lambda r: r["exp"])
        _ex_names= [r["name"][:11]  for r in _ex_s]
        _ex_vals = [r["exp"]        for r in _ex_s]
        _ex_cols = [
            "#ff3366" if r["exp"] <= 3 else
            "#ffbb00" if r["exp"] <= 7 else
            "#00cfff" if r["exp"] <= 30 else "#00ff88"
            for r in _ex_s
        ]

        # Urgency (sorted high→low)
        _ug_s    = sorted(_rows, key=lambda r: -r["urgency"])
        _ug_names= [r["name"][:11]  for r in _ug_s]
        _ug_vals = [r["urgency"]    for r in _ug_s]
        _ug_stk  = [r["stk"]        for r in _ug_s]
        _ug_rop  = [r["rop"]        for r in _ug_s]
        _ug_cols = [
            "#ff3366" if v >= 70 else
            "#ffbb00" if v >= 30 else "#00ff88"
            for v in _ug_vals
        ]

        # Trend line for scatter (simple linear regression)
        _n = len(_hm_x)
        _sx  = sum(_hm_x); _sy = sum(_hm_y)
        _sx2 = sum(v*v for v in _hm_x)
        _sxy = sum(_hm_x[i]*_hm_y[i] for i in range(_n))
        _denom = (_n * _sx2 - _sx * _sx) or 1
        _slope = (_n * _sxy - _sx * _sy) / _denom
        _inter = (_sy - _slope * _sx) / _n
        _tx_min = round(min(_hm_x) - 3, 1)
        _tx_max = round(max(_hm_x) + 3, 1)
        _ty_min = round(max(0, _slope * _tx_min + _inter), 1)
        _ty_max = round(min(100, _slope * _tx_max + _inter), 1)

        _i2_data = {
            "ts": _now_ts,
            "rNames": _r_names, "rSS": _r_ss, "rES": _r_es, "rMS": _r_ms,
            "rOrd": _r_ord, "rRatio": _r_ratio, "rCols": _r_cols,
            "dLabels": _d_labels, "dVals": _d_vals, "dTotal": _d_total,
            "hmNames": _hm_names, "hmX": _hm_x, "hmY": _hm_y,
            "hmR": _hm_r, "hmCols": _hm_cols,
            "txMin": _tx_min, "txMax": _tx_max, "tyMin": _ty_min, "tyMax": _ty_max,
            "mrNames": _mr_names, "mrVals": _mr_vals,
            "mrSells": _mr_sells, "mrCosts": _mr_costs, "mrCols": _mr_cols,
            "exNames": _ex_names, "exVals": _ex_vals, "exCols": _ex_cols,
            "ugNames": _ug_names, "ugVals": _ug_vals,
            "ugStk": _ug_stk, "ugRop": _ug_rop, "ugCols": _ug_cols,
            "aItems": _a_items or "—", "bItems": _b_items or "—",
            "cItems": _c_items or "—",
        }
        _i2_json = _json.dumps(_i2_data)

        _iframe2 = """<!DOCTYPE html><html><head>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#0a0e1a;color:#e0e8ff;font-family:'Segoe UI',monospace,sans-serif;padding:14px}
.g2{display:grid;grid-template-columns:1fr 1fr;gap:14px;margin-bottom:14px}
.g3{display:grid;grid-template-columns:1.4fr 1fr;gap:14px;margin-bottom:14px}
.panel{background:linear-gradient(135deg,#0d1224,#111827);border:1px solid #1e3a5f;
  border-radius:12px;padding:14px;position:relative;overflow:hidden}
.panel::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;
  background:linear-gradient(90deg,#00ff88,#00cfff,#a855f7)}
.pt{font-size:.72rem;font-weight:700;color:#7dd3fc;letter-spacing:.7px;
    text-transform:uppercase;margin-bottom:6px}
.sub{font-size:.60rem;color:#94a3b8;margin-bottom:10px}
canvas{max-width:100%}
.hrow{display:flex;align-items:center;gap:7px;margin:5px 0}
.hl{width:105px;font-size:.64rem;color:#cbd5e1;flex-shrink:0;
    overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.ht{flex:1;height:13px;background:#1e2a3a;border-radius:7px;overflow:hidden}
.hf{height:100%;border-radius:7px}
.hv{width:36px;font-size:.62rem;text-align:right;flex-shrink:0;font-weight:700}
.htag{width:46px;font-size:.58rem;text-align:right;flex-shrink:0}
.dleg{margin-top:8px}
.dr{display:flex;align-items:center;gap:6px;font-size:.66rem;margin:3px 0}
.dd{width:10px;height:10px;border-radius:50%;flex-shrink:0}
.abc{display:grid;grid-template-columns:1fr 1fr 1fr;gap:6px;margin-top:10px}
.ac{background:#0a0e1a;border-radius:8px;padding:8px;text-align:center;border:1px solid #1e3a5f}
.al{font-size:1.4rem;font-weight:900}
.alb{font-size:.58rem;color:#94a3b8;margin-top:2px}
.ai{font-size:.60rem;color:#cbd5e1;margin-top:3px;line-height:1.4}
.ql{position:absolute;font-size:.58rem;font-weight:700;letter-spacing:.3px;
    opacity:.45;pointer-events:none}
</style></head><body>
<script>
const D=""" + _i2_json + """;
const GC='rgba(30,58,95,0.6)',LC='#7dd3fc',TC='#94a3b8';
Chart.defaults.color=TC;
Chart.defaults.font.family="'Segoe UI',monospace";
Chart.defaults.font.size=11;
const dColors=['#00ff88','#ffbb00','#ff3366','#a855f7'];

// ── Section header ────────────────────────────────────────────────────
document.write('<div style="display:flex;justify-content:space-between;'
  +'align-items:center;margin-bottom:12px;">'
  +'<div style="font-size:.68rem;color:#7dd3fc;font-weight:700;letter-spacing:.5px;">'
  +'📊 INVENTORY INTELLIGENCE SUITE  ·  6 PANELS</div>'
  +'<div style="font-size:.62rem;color:#475569;">🕐 '+D.ts+'</div></div>');

// ══════════════════════════════════════════════════════════════════════
// ROW 1: Radar-as-Line + Donut
// ══════════════════════════════════════════════════════════════════════
document.write('<div class="g2"><div class="panel" id="pRadar"></div>'
              +'<div class="panel" id="pDonut"></div></div>');

// Panel: Multi-dimension line
const pR = document.getElementById('pRadar');
pR.innerHTML = '<div class="pt">🕸️ Multi-Dimension Intelligence · Top 6 SKUs by Health Score</div>'
  +'<div class="sub">Axes: Stock · Expiry · Margin · Order Readiness · Fill Ratio — line per dimension</div>'
  +'<div style="position:relative;height:280px"><canvas id="cRadar"></canvas></div>';
new Chart(document.getElementById('cRadar'),{
  type:'line',
  data:{
    labels:D.rNames,
    datasets:[
      {label:'Stock Score',data:D.rSS,borderColor:'#00ff88',backgroundColor:'rgba(0,255,136,.07)',
       borderWidth:2,tension:.35,fill:false,pointRadius:5,pointHoverRadius:8,animation:false},
      {label:'Expiry Score',data:D.rES,borderColor:'#00cfff',backgroundColor:'rgba(0,207,255,.07)',
       borderWidth:2,tension:.35,fill:false,pointRadius:5,pointHoverRadius:8,animation:false},
      {label:'Margin Score',data:D.rMS,borderColor:'#a855f7',backgroundColor:'rgba(168,85,247,.07)',
       borderWidth:2,tension:.35,fill:false,pointRadius:5,pointHoverRadius:8,animation:false},
      {label:'Order Readiness',data:D.rOrd,borderColor:'#ffbb00',backgroundColor:'rgba(255,187,0,.07)',
       borderWidth:2,tension:.35,fill:false,pointRadius:5,pointHoverRadius:8,animation:false},
      {label:'Fill Ratio×50',data:D.rRatio,borderColor:'#f97316',backgroundColor:'rgba(249,115,22,.07)',
       borderWidth:2,tension:.35,fill:false,pointRadius:5,pointHoverRadius:8,animation:false},
    ]
  },
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{
      legend:{labels:{color:LC,boxWidth:12,font:{size:10},usePointStyle:true}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',padding:10,
        callbacks:{title:ctx=>'📦 '+ctx[0].label}}
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC,maxRotation:28,font:{size:9}}},
      y:{grid:{color:GC},ticks:{color:TC},min:0,max:100,
         title:{display:true,text:'Score (0–100)',color:LC}}
    }
  }
});

// Panel: Donut
const pD = document.getElementById('pDonut');
pD.innerHTML = '<div class="pt">🍩 Portfolio Status Distribution · '+D.dTotal+' SKUs Total</div>'
  +'<div class="sub">Healthy / Watch / Critical / Overstock — live from DB</div>'
  +'<div style="position:relative;height:200px"><canvas id="cDonut"></canvas></div>'
  +'<div class="dleg" id="dLeg"></div>';

const dChart = new Chart(document.getElementById('cDonut'),{
  type:'doughnut',
  data:{labels:D.dLabels,datasets:[{
    data:D.dVals,backgroundColor:dColors.map(c=>c+'bb'),
    borderColor:dColors,borderWidth:2,hoverOffset:6
  }]},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,cutout:'63%',
    plugins:{
      legend:{display:false},
      tooltip:{callbacks:{label:ctx=>' '+ctx.label+': '+ctx.parsed+' SKUs'}}
    }
  }
});
// Center text via timeout
setTimeout(()=>{
  const ch=dChart,c=ch.ctx,ca=ch.chartArea;
  if(!ca) return;
  const cx=ca.left+(ca.right-ca.left)/2, cy=ca.top+(ca.bottom-ca.top)/2;
  c.save();
  c.font='bold 22px Segoe UI';c.fillStyle='#00ff88';
  c.textAlign='center';c.textBaseline='middle';
  c.fillText(D.dTotal,cx,cy-9);
  c.font='11px Segoe UI';c.fillStyle=LC;
  c.fillText('SKUs',cx,cy+10);
  c.restore();
},80);
// Legend
const legEl=document.getElementById('dLeg');
D.dLabels.forEach((l,i)=>{
  legEl.innerHTML+='<div class="dr"><div class="dd" style="background:'+dColors[i]+'"></div>'
    +'<span style="color:#cbd5e1">'+l+'</span>'
    +'<span style="color:'+LC+';margin-left:auto;font-weight:700">'+D.dVals[i]+'</span></div>';
});

// ══════════════════════════════════════════════════════════════════════
// ROW 2: Health vs Margin scatter + Urgency
// ══════════════════════════════════════════════════════════════════════
document.write('<div class="g3"><div class="panel" id="pHM"></div>'
              +'<div class="panel" id="pUrg"></div></div>');

// Health vs Margin
const pHM = document.getElementById('pHM');
pHM.innerHTML = '<div class="pt">💹 Health Score vs Gross Margin · Bubble Size = Stock Qty</div>'
  +'<div class="sub">Top-right = ideal (high margin + healthy stock)  ·  Bottom-left = action needed</div>'
  +'<div style="position:relative;height:270px">'
  +'<canvas id="cHM"></canvas>'
  +'<span class="ql" style="top:14px;right:14px;color:#00ff88">✅ IDEAL</span>'
  +'<span class="ql" style="bottom:18px;right:14px;color:#ffbb00">⚠️ LOW STOCK</span>'
  +'<span class="ql" style="top:14px;left:14px;color:#ffbb00">⏰ MARGIN RISK</span>'
  +'<span class="ql" style="bottom:18px;left:14px;color:#ff3366">🔴 CRITICAL</span>'
  +'</div>';

const hmDS = D.hmNames.map((nm,i)=>({
  label:nm,
  data:[{x:D.hmX[i],y:D.hmY[i],r:D.hmR[i]}],
  backgroundColor:D.hmCols[i]+'99',
  borderColor:D.hmCols[i],borderWidth:1.5
}));
hmDS.push({
  label:'Trend',type:'line',
  data:[{x:D.txMin,y:D.tyMin},{x:D.txMax,y:D.tyMax}],
  borderColor:'rgba(255,255,255,.18)',borderDash:[4,6],
  borderWidth:1,pointRadius:0,fill:false
});
new Chart(document.getElementById('cHM'),{
  type:'bubble',data:{datasets:hmDS},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'nearest',intersect:true},
    plugins:{
      legend:{labels:{color:LC,boxWidth:8,font:{size:8}}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',padding:10,
        callbacks:{
          title:ctx=>'📦 '+ctx[0].dataset.label,
          label:ctx=>{
            if(ctx.dataset.label==='Trend') return null;
            return['  Margin : '+ctx.raw.x.toFixed(1)+'%',
                   '  Health : '+ctx.raw.y+' / 100',
                   '  Stock  : ~'+(ctx.raw.r*8)+' units'];
          }
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC},
         title:{display:true,text:'Gross Margin %',color:LC},
         min:Math.min(...D.hmX)-5,max:Math.max(...D.hmX)+5},
      y:{grid:{color:GC},ticks:{color:TC},min:0,max:100,
         title:{display:true,text:'Health Score (0–100)',color:LC}}
    }
  }
});

// Urgency panel
const pUrg = document.getElementById('pUrg');
pUrg.innerHTML = '<div class="pt">⚡ Reorder Urgency · Sorted High → Low</div>'
  +'<div class="sub">0% = safe buffer · 100% = stockout imminent</div>'
  +'<div id="urgList"></div>'
  +'<div style="border-top:1px solid #1e3a5f;padding-top:10px;margin-top:10px">'
  +'<div style="font-size:.62rem;color:#7dd3fc;margin-bottom:6px">URGENCY TREND LINE</div>'
  +'<div style="position:relative;height:120px"><canvas id="cUrg"></canvas></div></div>';
const urgEl=document.getElementById('urgList');
D.ugNames.forEach((nm,i)=>{
  const col=D.ugCols[i];
  const tag=D.ugVals[i]>=70?'ORDER NOW':D.ugVals[i]>=30?'Watch':'OK';
  urgEl.innerHTML+='<div class="hrow">'
    +'<div class="hl">'+nm+'</div>'
    +'<div class="ht"><div class="hf" style="width:'+D.ugVals[i]+'%;background:'+col+'"></div></div>'
    +'<div class="hv" style="color:'+col+'">'+D.ugVals[i]+'%</div>'
    +'<div class="htag" style="color:'+col+'">'+tag+'</div>'
    +'</div>';
});
new Chart(document.getElementById('cUrg'),{
  type:'line',
  data:{labels:D.ugNames,datasets:[
    {label:'Urgency %',data:D.ugVals,borderColor:'#ff3366',
     backgroundColor:'rgba(255,51,102,.08)',borderWidth:2,tension:.35,fill:true,
     pointBackgroundColor:D.ugCols,pointBorderColor:D.ugCols,
     pointRadius:5,pointHoverRadius:8,animation:false},
    {label:'0%',data:D.ugNames.map(()=>0),borderColor:'rgba(0,255,136,.2)',
     borderDash:[3,5],borderWidth:1,pointRadius:0,fill:false}
  ]},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:LC,boxWidth:10,font:{size:9}}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',
        callbacks:{title:ctx=>'⚡ '+ctx[0].label,
          label:ctx=>ctx.datasetIndex===1?null:'  Urgency: '+ctx.raw+'%',
          afterLabel:ctx=>{
            if(ctx.datasetIndex===1) return null;
            const i=ctx.dataIndex;
            return'  Stock: '+D.ugStk[i]+'  ROP: '+D.ugRop[i];
          }
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC,font:{size:8},maxRotation:30}},
      y:{grid:{color:GC},ticks:{color:TC},min:0,max:100,
         title:{display:true,text:'Urgency %',color:LC,font:{size:9}}}
    }
  }
});

// ══════════════════════════════════════════════════════════════════════
// ROW 3: Expiry + Margin+ABC
// ══════════════════════════════════════════════════════════════════════
document.write('<div class="g2"><div class="panel" id="pExp"></div>'
              +'<div class="panel" id="pMar"></div></div>');

// Expiry panel
const pExp = document.getElementById('pExp');
pExp.innerHTML = '<div class="pt">⏰ Expiry Countdown · Days Remaining (capped 90d) · Urgent First</div>'
  +'<div class="sub">🚨 &lt;3d · ⏰ &lt;7d · 🟡 &lt;30d · 🟢 Safe</div>'
  +'<div id="expList"></div>'
  +'<div style="border-top:1px solid #1e3a5f;padding-top:10px;margin-top:10px">'
  +'<div style="font-size:.62rem;color:#7dd3fc;margin-bottom:6px">EXPIRY LINE CHART</div>'
  +'<div style="position:relative;height:130px"><canvas id="cExp"></canvas></div></div>';
const expEl=document.getElementById('expList');
D.exNames.forEach((nm,i)=>{
  const col=D.exCols[i];
  const pct=Math.min(D.exVals[i]/90*100,100);
  const flag=D.exVals[i]<=1?'🚨':D.exVals[i]<=3?'🔴':D.exVals[i]<=7?'⏰':D.exVals[i]<=30?'🟡':'🟢';
  const tag=D.exVals[i]<=3?'URGENT':D.exVals[i]<=7?'Soon':D.exVals[i]<=30?'Watch':'OK';
  expEl.innerHTML+='<div class="hrow">'
    +'<div class="hl">'+flag+' '+nm+'</div>'
    +'<div class="ht"><div class="hf" style="width:'+pct+'%;'
    +'background:linear-gradient(90deg,'+col+'88,'+col+')"></div></div>'
    +'<div class="hv" style="color:'+col+'">'+D.exVals[i]+'d</div>'
    +'<div class="htag" style="color:'+col+'">'+tag+'</div>'
    +'</div>';
});
new Chart(document.getElementById('cExp'),{
  type:'line',
  data:{labels:D.exNames,datasets:[
    {label:'Days to Expiry',data:D.exVals,borderColor:'#00cfff',
     backgroundColor:'rgba(0,207,255,.07)',borderWidth:2,tension:.35,fill:true,
     pointBackgroundColor:D.exCols,pointBorderColor:D.exCols,
     pointRadius:5,pointHoverRadius:8,animation:false},
    {label:'7d Warning',data:D.exNames.map(()=>7),borderColor:'rgba(255,187,0,.35)',
     borderDash:[4,5],borderWidth:1,pointRadius:0,fill:false},
    {label:'3d Critical',data:D.exNames.map(()=>3),borderColor:'rgba(255,51,102,.45)',
     borderDash:[2,6],borderWidth:1,pointRadius:0,fill:false}
  ]},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:LC,boxWidth:10,font:{size:9}}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',
        callbacks:{title:ctx=>'⏰ '+ctx[0].label,
          label:ctx=>{
            if(ctx.datasetIndex>0) return'  '+ctx.dataset.label+': '+ctx.raw+'d';
            const v=ctx.raw;
            return v<=3?'  🚨 URGENT: '+v+'d':v<=7?'  ⏰ Soon: '+v+'d':'  🟢 '+v+'d remaining';
          }
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC,font:{size:8},maxRotation:30}},
      y:{grid:{color:GC},ticks:{color:TC},min:0,
         title:{display:true,text:'Days Remaining',color:LC,font:{size:9}}}
    }
  }
});

// Margin + ABC panel
const pMar = document.getElementById('pMar');
pMar.innerHTML = '<div class="pt">💰 Gross Margin % · Line Chart · Sorted Low → High</div>'
  +'<div class="sub">Green ≥25% · Cyan ≥12% · Yellow ≥0% · Red &lt;0% — with ABC classification</div>'
  +'<div style="position:relative;height:210px"><canvas id="cMar"></canvas></div>'
  +'<div class="abc" id="abcG"></div>';

new Chart(document.getElementById('cMar'),{
  type:'line',
  data:{labels:D.mrNames,datasets:[
    {label:'Gross Margin %',data:D.mrVals,borderColor:'#a855f7',
     backgroundColor:'rgba(168,85,247,.07)',borderWidth:2.5,tension:.35,fill:true,
     pointBackgroundColor:D.mrCols,pointBorderColor:D.mrCols,
     pointRadius:6,pointHoverRadius:9,animation:false},
    {label:'25% Target',data:D.mrNames.map(()=>25),borderColor:'rgba(0,255,136,.35)',
     borderDash:[5,5],borderWidth:1.2,pointRadius:0,fill:false},
    {label:'12% Floor',data:D.mrNames.map(()=>12),borderColor:'rgba(255,187,0,.35)',
     borderDash:[3,6],borderWidth:1.2,pointRadius:0,fill:false},
    {label:'Break-even',data:D.mrNames.map(()=>0),borderColor:'rgba(255,51,102,.30)',
     borderDash:[2,7],borderWidth:1,pointRadius:0,fill:false}
  ]},
  options:{
    responsive:true,maintainAspectRatio:false,animation:false,
    interaction:{mode:'index',intersect:false},
    plugins:{legend:{labels:{color:LC,boxWidth:10,font:{size:9}}},
      tooltip:{backgroundColor:'rgba(10,14,26,.96)',borderColor:'#1e3a5f',borderWidth:1,
        titleColor:LC,bodyColor:'#cbd5e1',padding:10,
        callbacks:{title:ctx=>'💰 '+ctx[0].label,
          label:ctx=>{
            if(ctx.datasetIndex>0) return'  '+ctx.dataset.label+': '+ctx.raw+'%';
            const i=ctx.dataIndex;
            return['  Margin : '+ctx.raw.toFixed(1)+'%',
                   '  Sell ৳ : '+D.mrSells[i],
                   '  Cost ৳ : '+D.mrCosts[i]];
          }
        }
      }
    },
    scales:{
      x:{grid:{color:GC},ticks:{color:TC,maxRotation:32,font:{size:9}}},
      y:{grid:{color:GC},ticks:{color:TC},
         title:{display:true,text:'Gross Margin %',color:LC},
         suggestedMin:-5,suggestedMax:40}
    }
  }
});

// ABC grid
document.getElementById('abcG').innerHTML =
  '<div class="ac"><div class="al" style="color:#00ff88">A</div>'
  +'<div class="alb">High Value (Top 20%)</div>'
  +'<div class="ai">'+D.aItems+'</div></div>'
  +'<div class="ac"><div class="al" style="color:#00cfff">B</div>'
  +'<div class="alb">Medium Value (20–50%)</div>'
  +'<div class="ai">'+D.bItems+'</div></div>'
  +'<div class="ac"><div class="al" style="color:#94a3b8">C</div>'
  +'<div class="alb">Low Value (bottom 50%)</div>'
  +'<div class="ai">'+D.cItems+'</div></div>';

</script></body></html>"""

        components.html(_iframe2, height=1700, scrolling=False)

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 1 — INVENTORY
    # ═════════════════════════════════════════════════════════════════════════

    def _t1_inventory(self, inv: List[Dict], prices: Dict, event: str) -> None:
        st.markdown("## 📦 Inventory Management")
        t_view, t_eoq, t_price = st.tabs(["📋 Stock Table","📐 EOQ Calculator","💲 Dynamic Pricing"])

        with t_view:
            st.markdown("### Current Stock Levels")
            if PANDAS_AVAILABLE and inv:
                rows = []
                for item in inv:
                    sid   = item.get("sku_id","")
                    stk   = item.get("current_stock",0)
                    rop   = item.get("reorder_point",20)
                    eoq   = item.get("eoq",50)
                    exp   = item.get("expiry_days",30)
                    cost  = item.get("unit_cost",0)
                    p_inf = prices.get(sid,{})
                    sell  = p_inf.get("price",cost)
                    marg  = round((sell-cost)/max(sell,1)*100,1)
                    stat  = ("🔴 CRITICAL" if stk<rop*0.5 else
                             "🟡 LOW"      if stk<rop else
                             "🟣 OVERSTOCK" if stk>eoq*2.5 else "🟢 OK")
                    eflag = "🚨" if exp<=2 else ("⏰" if exp<=5 else "")
                    rows.append({
                        "SKU": item.get("name",sid), "Category": item.get("category",""),
                        "Stock": stk, "Reorder@": rop, "EOQ": eoq, "Status": stat,
                        "Expiry": f"{eflag}{exp}d", "Cost৳": cost, "Sell৳": sell,
                        "Margin%": marg, "Supplier": item.get("supplier",""),
                        "DataSrc": p_inf.get("data_source","?"),
                    })
                st.dataframe(pd.DataFrame(rows), use_container_width=True, height=400)
            else:
                for item in inv: st.write(item)

            st.divider()
            st.markdown("### ✏️ Update Stock")
            sku_map = {i.get("sku_id",""): i.get("name","?") for i in inv}
            cu1,cu2,cu3 = st.columns(3)
            with cu1: edit_sku = st.selectbox("SKU",list(sku_map.keys()),format_func=lambda x:sku_map.get(x,x),key="inv_sku")
            with cu2: edit_qty = st.number_input("New Stock",min_value=0,value=50,key="inv_qty")
            with cu3: edit_exp = st.number_input("Expiry (days)",min_value=0,value=7,key="inv_exp")
            if st.button("💾 Save Changes",key="inv_save"):
                self.db.execute_query(
                    "UPDATE inventory SET current_stock=?,expiry_days=?,updated_at=datetime('now') WHERE sku_id=?",
                    (edit_qty, edit_exp, edit_sku),
                )
                self.log_action(
                    "STOCK_UPDATE",
                    f"Stock updated: {sku_map.get(edit_sku, edit_sku)} → "
                    f"qty={edit_qty}, expiry={edit_exp}d",
                )
                st.success(f"Updated {sku_map.get(edit_sku,edit_sku)}: {edit_qty} units, {edit_exp}d expiry")
                st.rerun()

        with t_eoq:
            st.markdown("### 📐 Wilson Economic Order Quantity")
            st.info("Calculates optimal order quantity minimising total annual inventory cost.")
            c1,c2,c3,c4 = st.columns(4)
            with c1: eoq_sku = st.selectbox("SKU",[i["sku_id"] for i in inv],format_func=lambda x:SKUS.get(x,("?",""))[0],key="eoq_sku")
            with c2: d_yr    = st.number_input("Annual demand",min_value=1,value=3000,key="eoq_d")
            with c3: o_cost  = st.number_input("Order cost (৳/PO)",min_value=1,value=250,key="eoq_s")
            with c4: h_rate  = st.slider("Holding rate %/yr",5,50,25,key="eoq_h") / 100
            if st.button("⚙️ Compute EOQ",key="eoq_btn"):
                res = self.business.calculate_eoq(eoq_sku, d_yr, o_cost, h_rate)
                ss  = self.business.calculate_safety_stock(d_yr/365, d_yr/365*0.15)
                c1,c2,c3,c4 = st.columns(4)
                c1.metric("EOQ",             f'{res["eoq"]:.0f} units')
                c2.metric("Orders/Year",     f'{res["annual_orders"]:.1f}')
                c3.metric("Cycle (days)",    f'{res["cycle_time_days"]:.1f}')
                c4.metric("Total Ann. Cost", f'৳{res["total_annual_cost"]:,.0f}')
                c5,c6,c7 = st.columns(3)
                c5.metric("Safety Stock",    f'{ss["safety_stock"]:.0f}')
                c6.metric("Reorder Point",   f'{ss["reorder_point"]:.0f}')
                c7.metric("Service Level",   f'{ss["service_level"]*100:.0f}%')
                self.db.execute_query(
                    "UPDATE inventory SET eoq=?,reorder_point=? WHERE sku_id=?",
                    (int(res["eoq"]), int(ss["reorder_point"]), eoq_sku),
                )
                st.success("EOQ and reorder point saved to DB.")

        with t_price:
            st.markdown("### 💲 Dynamic Pricing Engine")
            st.info("Adjusts sell price based on expiry pressure, scarcity, overstock, and event demand.")
            if PANDAS_AVAILABLE:
                rows = []
                for item in inv:
                    sid  = item.get("sku_id","")
                    base = prices.get(sid,{}).get("price", item.get("unit_cost",0)) or item.get("unit_cost",0)
                    res  = self.business.dynamic_price(sid, base,
                                                       stock=item.get("current_stock",50),
                                                       eoq=item.get("eoq",50),
                                                       expiry=item.get("expiry_days",30),
                                                       event=event)
                    rows.append({
                        "SKU": item.get("name",sid), "Base৳": base,
                        "Adj৳": res["adjusted_price"], "Chg%": f'{res["discount_pct"]:+.1f}%',
                        "Reason": res["reason"][:55],
                    })
                st.dataframe(pd.DataFrame(rows), use_container_width=True)
            st.divider()
            st.markdown("**Single-SKU Price Simulator**")
            ps1,ps2,ps3,ps4 = st.columns(4)
            with ps1: ps_sku  = st.selectbox("SKU",[i["sku_id"] for i in inv],format_func=lambda x:SKUS.get(x,("?",""))[0],key="ps_sku")
            with ps2: ps_base = st.number_input("Base ৳",min_value=1.0,value=100.0,key="ps_base")
            with ps3: ps_stk  = st.number_input("Stock",min_value=0,value=30,key="ps_stk")
            with ps4: ps_exp  = st.number_input("Expiry d",min_value=0,value=7,key="ps_exp")
            if st.button("💡 Simulate",key="ps_btn"):
                res = self.business.dynamic_price(ps_sku, ps_base, stock=ps_stk, eoq=50, expiry=ps_exp, event=event)
                a,b,c = st.columns(3)
                a.metric("Base",     f"৳{ps_base}")
                b.metric("Adjusted", f"৳{res['adjusted_price']}")
                c.metric("Change",   f"{res['discount_pct']:+.1f}%")
                st.info(f"Reason: {res['reason']}")

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 2 — AI INTELLIGENCE
    # ═════════════════════════════════════════════════════════════════════════

    def _t2_ai(self, inv: List[Dict], prices: Dict, weather: Dict,
               event: str, fcs: Dict) -> None:
        st.markdown("## 🧠 AI Intelligence Engine")
        t_fc, t_sku, t_proc = st.tabs(["📈 Demand Forecast","🔍 SKU Deep Dive","📋 Procurement Plan"])

        with t_fc:
            st.markdown(f"### 7-Day Demand Forecast")
            _fc_method_label = "LSTM (TF) — non-blocking background training" if TF_AVAILABLE else "Holt's Linear Trend"
            st.caption(f"Method: {_fc_method_label}  |  Event: {event}")
            if st.button("🔮 Run All Forecasts",key="fc_run"):
                with st.spinner("Forecasting… (LSTM trains in background; Holt's used until ready)"):
                    new_fc = {i.get("sku_id",""): self.soptom.forecast_demand(i.get("sku_id",""),event=event) for i in inv}
                    st.session_state["forecasts"] = new_fc
                    fcs = new_fc
                # Show how many SKUs used each method
                if fcs:
                    methods     = [v.get("method","?") for v in fcs.values()]
                    lstm_count  = methods.count("lstm")
                    holts_count = methods.count("holts_linear_trend")
                    bg_training = sum(
                        1 for s in SKUS
                        if SoptomAlgorithm._lstm_bg_training.get(s, False)
                    )
                    status_parts = []
                    if lstm_count:  status_parts.append(f"✅ {lstm_count} LSTM (cached)")
                    if holts_count: status_parts.append(f"📊 {holts_count} Holt's Linear Trend")
                    if bg_training: status_parts.append(
                        f"⏳ {bg_training} LSTM training in background — re-run forecasts in a moment"
                    )
                    if status_parts:
                        st.info("  ·  ".join(status_parts))

            if fcs:
                for item in inv:
                    sid  = item.get("sku_id","")
                    fc   = fcs.get(sid)
                    if not fc: continue
                    fv   = fc.get("forecast",[])
                    with st.expander(f"📦 {item.get('name',sid)} — Peak D{fc.get('peak_day',1)} | Conf {fc.get('confidence',0.5)*100:.0f}% [{fc.get('method','?')}]"):
                        cl,cr = st.columns([3,1])
                        with cl:
                            st.markdown(_spark_bar(fv,color="#00cfff"), unsafe_allow_html=True)
                            for d,v in zip(["D1","D2","D3","D4","D5","D6","D7"],fv):
                                st.write(f"  {d}: **{v:.1f}** units")
                        with cr:
                            avg = sum(fv)/max(len(fv),1)
                            stk = item.get("current_stock",50)
                            st.metric("Peak Day",  f"D{fc.get('peak_day',1)}")
                            st.metric("Confidence",f"{fc.get('confidence',0.5)*100:.0f}%")
                            st.metric("Event ×",   f"{fc.get('event_factor',1.0):.2f}")
                            st.metric("Days Cover",f"{round(stk/max(avg,1),1)} d")
            else:
                st.info("Click 'Run All Forecasts' to generate predictions.")

        with t_sku:
            st.markdown("### 🔍 SKU Deep Intelligence")
            sku_map = {i.get("sku_id",""): i.get("name","?") for i in inv}
            col_s1, col_s2 = st.columns([2,1])
            with col_s1:
                deep_sku = st.selectbox("Select SKU",list(sku_map.keys()),format_func=lambda x:sku_map.get(x,x),key="deep_sku")
            with col_s2:
                if st.button("🧠 Analyse",key="deep_btn"):
                    item_    = next((i for i in inv if i.get("sku_id")==deep_sku),{})
                    sku_data = {**item_, **prices.get(deep_sku,{})}
                    fc_data  = fcs.get(deep_sku) or self.soptom.forecast_demand(deep_sku, event=event)
                    with st.spinner("Generating deep analysis…"):
                        analysis = self.soptom.analyze_sku_deep(deep_sku, sku_data, fc_data, weather)
                        self.db.log_ai_event("sku_deep", deep_sku, sku_data, analysis, self.soptom.get_model_name())
                        st.session_state[f"deep_{deep_sku}"] = (analysis, fc_data)

            key = f"deep_{deep_sku}"
            if key in st.session_state:
                analysis, fc_data = st.session_state[key]
                item_ = next((i for i in inv if i.get("sku_id")==deep_sku),{})
                m1,m2,m3,m4 = st.columns(4)
                m1.metric("Stock",       item_.get("current_stock","?"))
                m2.metric("EOQ",         item_.get("eoq","?"))
                m3.metric("Expiry",      f'{item_.get("expiry_days","?")} d')
                p_inf = prices.get(deep_sku,{})
                src   = p_inf.get("data_source","?")
                m4.metric("Price",       f'৳{p_inf.get("price","?")}')
                st.markdown(
                    f'<div class="nx-card"><p style="font-size:.75rem;color:#7dd3fc;">Data: {src}</p>'
                    f'<p>{analysis}</p></div>',
                    unsafe_allow_html=True,
                )
                hist = self.db.get_price_history(deep_sku, limit=20)
                if hist:
                    ph = [h.get("price",0) for h in reversed(hist)]
                    st.markdown("**📉 Price History**")
                    st.markdown(_spark_bar(ph,"#ffbb00",50), unsafe_allow_html=True)
                    st.caption(f"Sources: {set(h.get('data_source','?') for h in hist)}")

        with t_proc:
            st.markdown("### 📋 AI Procurement Plan Generator")
            if st.button("📋 Generate 7-Day Plan",key="proc_gen"):
                fc_all = fcs or {i.get("sku_id",""): self.soptom.forecast_demand(i.get("sku_id",""),event=event) for i in inv}
                st.session_state["forecasts"] = fc_all
                with st.spinner("Generating procurement plan…"):
                    plan = self.soptom.generate_procurement_plan(inv, fc_all, event)
                    self.db.log_ai_event("procurement","all",{"event":event},plan,self.soptom.get_model_name())
                    st.session_state["proc_plan"] = plan

            # ── FIX: download_button always rendered (not inside button block) ──
            if "proc_plan" in st.session_state:
                plan_text = st.session_state["proc_plan"]
                st.markdown(
                    f'<div class="nx-card"><p style="white-space:pre-wrap;">{plan_text}</p></div>',
                    unsafe_allow_html=True,
                )
                fname = f"procurement_{event.replace(' ','_')}_{datetime.date.today()}.txt"
                st.download_button(
                    label="⬇️ Download Plan (.txt)",
                    data=str(plan_text).encode("utf-8") if plan_text else b"",
                    file_name=fname,
                    mime="text/plain",
                    key="dl_proc",
                )
            else:
                st.info("Click 'Generate 7-Day Plan' to create an AI-powered plan based on live data.")

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 3 — DSS ENGINE
    # ═════════════════════════════════════════════════════════════════════════

    def _t3_dss(self, inv: List[Dict], prices: Dict, fcs: Dict) -> None:
        st.markdown("## ⚖️ Decision Support System (MCDA)")
        st.caption("5-criteria weighted scoring · Normalised 0-1 per criterion")

        # Compute forecasts for DSS if not available
        fc_for_dss = fcs if fcs else {
            i.get("sku_id",""): self.soptom.forecast_demand(i.get("sku_id","")) for i in inv
        }

        t_rank, t_explain, t_sens = st.tabs(["🏆 Ranking","🔎 Explain","📊 Sensitivity"])

        with t_rank:
            ranked = self.dss.rank_skus(inv, fc_for_dss, prices)

            if PANDAS_AVAILABLE:
                rows = [{
                    "Rank": idx+1, "SKU": r["name"], "Category": r["category"],
                    "Score": f'{r["total_score"]:.3f}',
                    "Action": r["action"],
                    "Demand": f'{r["demand_score"]:.2f}',
                    "Price":  f'{r["price_score"]:.2f}',
                    "Stock":  f'{r["stock_score"]:.2f}',
                    "Expiry": f'{r["expiry_score"]:.2f}',
                    "Margin": f'{r["margin_score"]:.2f}',
                } for idx,r in enumerate(ranked)]
                st.dataframe(pd.DataFrame(rows), use_container_width=True, height=400)
            else:
                for r in ranked: st.write(f"{r['name']}: {r['total_score']:.3f} → {r['action']}")

            # Save to DB on button press, not on every render
            if st.button("💾 Save DSS Scores to DB",key="dss_save"):
                for r in ranked:
                    self.db.log_dss_score(r["sku_id"], r, r["action"])
                st.success(f"Saved {len(ranked)} DSS scores.")

            st.divider()
            act_cnts: Dict[str,int] = defaultdict(int)
            for r in ranked: act_cnts[r["action"]] += 1
            c1,c2,c3,c4,c5 = st.columns(5)
            for col_, (act, cls) in zip(
                [c1,c2,c3,c4,c5],
                [("CRITICAL_ORDER","badge-critical"),("URGENT_ORDER","badge-urgent"),
                 ("MONITOR","badge-monitor"),("STABLE","badge-stable"),("OVERSTOCK","badge-overstock")],
            ):
                col_.markdown(
                    f'<div class="nx-card" style="text-align:center;">'
                    f'<span class="{cls}">{act}<br>{act_cnts[act]}</span></div>',
                    unsafe_allow_html=True,
                )

        with t_explain:
            ranked_exp = self.dss.rank_skus(inv, fc_for_dss, prices)
            if ranked_exp:
                sku_opts = {r["sku_id"]: r["name"] for r in ranked_exp}
                sel = st.selectbox("SKU to explain",list(sku_opts.keys()),format_func=lambda x:sku_opts.get(x,x),key="dss_ex")
                sel_row = next((r for r in ranked_exp if r["sku_id"]==sel), None)
                if sel_row:
                    exp_txt = self.dss.explain_score(sel_row)
                    st.markdown(
                        f'<div class="nx-card"><pre style="color:#d0daf0;font-size:.88rem;">{exp_txt}</pre></div>',
                        unsafe_allow_html=True,
                    )
                    # Score bars
                    crits  = ["demand_score","price_score","stock_score","expiry_score","margin_score"]
                    bar_h  = ""
                    for c in crits:
                        val  = sel_row.get(c,0)
                        w    = int(val*200)
                        col  = "#00ff88" if val>0.6 else ("#ffbb00" if val>0.3 else "#ff3366")
                        lbl  = c.replace("_score","").title()
                        bar_h += (
                            f'<div style="margin:4px 0;">'
                            f'<span style="display:inline-block;width:80px;font-size:.78rem;color:#7dd3fc;">{lbl}</span>'
                            f'<div style="display:inline-block;height:13px;width:{w}px;background:{col};border-radius:3px;vertical-align:middle;"></div>'
                            f'<span style="font-size:.78rem;margin-left:6px;color:#e0e8ff;">{val:.3f}</span></div>'
                        )
                    st.markdown(f'<div class="nx-card">{bar_h}</div>', unsafe_allow_html=True)

        with t_sens:
            st.markdown("### Monte-Carlo Sensitivity Analysis")
            if st.button("🎲 Run 50-Trial Analysis", key="sens_btn"):
                with st.spinner("Running Monte-Carlo…"):
                    sens = self.dss.sensitivity_analysis(inv, fc_for_dss, prices, n_trials=50)
                    st.session_state["dss_sens"] = sens
            
            # --- সংশোধন শুরু ---
            sens = st.session_state.get("dss_sens") # ভেরিয়েবলটি নিরাপদভাবে নেওয়া
            if sens: # যদি sens এর মান থাকে তবেই নিচের কোডটি চলবে
                if PANDAS_AVAILABLE:
                    rows = [{"SKU":SKUS.get(sid,("?",""))[0], "Top-Rank %":v["top_rank_pct"], "Avg Rank":v["avg_rank"]}
                            for sid, v in sorted(sens.items(), key=lambda x:-x[1]["top_rank_pct"])]
                    st.dataframe(pd.DataFrame(rows), use_container_width=True)
                else: 
                    st.write(sens)
            else:
                st.info("Please click the 'Run 50-Trial Analysis' button to generate data.")
            # --- সংশোধন শেষ ---

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 4 — LIVE MAP
    # ═════════════════════════════════════════════════════════════════════════

    def _t4_map(self, inv: List[Dict], prices: Dict, fcs: Dict) -> None:
            st.markdown("## 🗺️ Live Delivery Map ")

            # ── Dependency check ──────────────────────────────────────────────────
            try:
                from streamlit_folium import st_folium  # type: ignore
                _sf_available = True
            except ImportError:
                _sf_available = False

            if not _sf_available or not self.maps._folium_available:
                st.error(
                    "**streamlit-folium** or **folium** is not installed.\n\n"
                    "Install both with:\n```\npip install folium streamlit-folium\n```\n\n"
                    "Then restart the Streamlit server."
                )
                return

            t_hub, t_route, t_bubble, t_rider = st.tabs([
                "🌐 Hub Network", "🛣️ Route Planner",
                "🫧 Demand Bubbles", "🏍️ Riders & Revenue",
            ])

            hub_metrics = self.routing.get_hub_metrics()
            closed_hubs = self.routing.get_closed_hubs()

            # ── Tab: Hub Network ──────────────────────────────────────────────────
            with t_hub:
                st.markdown("### Hub Network Map")
                st.caption(
                    "Node size ∝ betweenness centrality. "
                    "Edge colour: 🟢 low / 🟡 moderate / 🔴 heavy traffic."
                )
                col_ctrl, col_map = st.columns([1, 3])

                with col_ctrl:
                    st.markdown("**🔴 Close Hub**")
                    close_h = st.selectbox(
                        "Hub to close", ["— none —"] + list(DHAKA_HUBS.keys()), key="cl_hub"
                    )

                    # ── Action-Level Security: admin-only destructive action ────
                    is_admin_user = self.auth.is_admin() if self.auth else True
                    if st.button(
                        "Close", key="cl_btn",
                        disabled   = not is_admin_user,
                        help       = None if is_admin_user
                                     else "🔒 Admin access required to close hubs.",
                    ) and close_h != "— none —" and is_admin_user:
                        self.routing.close_hub(close_h)
                        self.db.add_alert(
                            "critical", "Logistics", f"Hub {close_h} CLOSED by operator."
                        )
                        self.log_action(
                            "HUB_CLOSE",
                            f"Hub '{close_h}' closed by {self.auth.current_user().get('username','?') if self.auth else 'operator'}.",
                        )
                        st.rerun()

                    st.markdown("**🟢 Reopen Hub**")
                    open_opts = closed_hubs if closed_hubs else ["— none —"]
                    open_h    = st.selectbox("Hub to reopen", open_opts, key="op_hub")
                    if st.button("Reopen", key="op_btn") and closed_hubs:
                        self.routing.reopen_hub(open_h)
                        st.rerun()

                    if closed_hubs:
                        st.error(f"Closed: {', '.join(closed_hubs)}")
                    else:
                        st.success("All hubs operational")

                    st.divider()
                    st.markdown("**Hub Metrics**")
                    for hm in hub_metrics:
                        status_icon = "🔴" if hm["hub"] in closed_hubs else "🟢"
                        st.markdown(
                            f'<div class="sb-metric">{status_icon} <b>{hm["hub"]}</b><br>'
                            f'Centrality: {hm.get("centrality", 0):.3f} | '
                            f'Degree: {hm.get("degree", 0)}</div>',
                            unsafe_allow_html=True,
                        )

                with col_map:
                    route_state  = st.session_state.get("last_route")

                    # ── Map engine selector ───────────────────────────────────
                    map_engine = st.radio(
                        "Map Engine",
                        ["Folium (2D)", "PyDeck 3D (WebGL)"],
                        horizontal=True,
                        key="hub_map_engine",
                    )
                    if map_engine == "PyDeck 3D (WebGL)" and self.pydeck:
                        self.pydeck.render_arc_map(hub_metrics, route_state, closed_hubs)
                    else:
                        hub_folium_m = self.maps.render_hub_map(
                            hub_metrics, route_state, closed_hubs
                        )
                        if hub_folium_m is not None:
                            st_folium(
                                hub_folium_m,
                                width            = "100%",
                                height           = 540,
                                returned_objects = [],
                                key              = "hub_map",
                            )

            # ── Tab: Route Planner ────────────────────────────────────────────────
            with t_route:
                st.markdown("### 🛣️ Optimal Route Planner")
                hubs       = list(DHAKA_HUBS.keys())
                r1, r2, r3 = st.columns(3)
                with r1: src  = st.selectbox("Origin",          hubs,        key="r_src")
                with r2: dst  = st.selectbox("Destination",     hubs, index=3, key="r_dst")
                with r3: mode = st.radio(
                    "Optimise for", ["balanced", "distance", "time"],
                    horizontal=True, key="r_mode",
                )

                if st.button("🔍 Find Route", key="r_btn"):
                    if src == dst:
                        st.warning("Origin and destination must be different hubs.")
                    else:
                        result = self.routing.find_optimal_route(src, dst, mode=mode)
                        if "error" not in result:
                            st.session_state["last_route"] = result
                            c1, c2, c3, c4 = st.columns(4)
                            c1.metric("Distance",  f'{result["total_km"]} km')
                            c2.metric("ETA",       f'{result["eta_min"]} min')
                            c3.metric("Hops",       result["hops"])
                            c4.metric("CO₂ Saved", f'{result.get("co2_saving_kg", 0):.3f} kg')
                            src_badge = result.get("data_source", "NetworkX")
                            if src_badge == "OSRM":
                                st.success(f"🛰️ **OSRM Real-Time Route**: **{' → '.join(result['path'])}**  |  Actual road geometry used.")
                            else:
                                st.success(f"Route [{src_badge}]: **{' → '.join(result['path'])}**")
                            savings = self.business.calculate_carbon_savings(
                                result.get("traditional_km", result["total_km"] * 1.3),
                                result["total_km"],
                            )
                            self.db.log_carbon(
                                f"{src}_{dst}_{int(time.time())}",
                                result.get("traditional_km", result["total_km"] * 1.3),
                                result["total_km"],
                                savings["fuel_saved"],
                                savings["co2_saved"],
                                savings["cost_saved"],
                            )
                            st.info(
                                f"💚 Saved: {savings['km_saved']:.2f} km | "
                                f"৳{savings['cost_saved']:.0f} | "
                                f"{savings['co2_saved']:.3f} kg CO₂"
                            )
                            st.rerun()
                        else:
                            st.error(result["error"])

                # Route map (always shows last computed route)
                if st.session_state.get("last_route"):
                    st.markdown("**Optimal route visualised:**")
                    route_folium_m = self.maps.render_hub_map(
                        hub_metrics,
                        st.session_state["last_route"],
                        closed_hubs,
                    )
                    if route_folium_m is not None:
                        st_folium(
                            route_folium_m,
                            width            = "100%",
                            height           = 460,
                            returned_objects = [],
                            key              = "route_map",
                        )

                st.divider()
                st.markdown("### 🔄 Multi-Stop Route Planner")
                mh = st.multiselect(
                    "Select Hubs (min 2)", hubs, default=hubs[:4], key="mh"
                )
                if st.button("📍 Plan Multi-Stop", key="ms_btn") and len(mh) >= 2:
                    plan = self.routing.plan_multi_stop(mh, optimize=True)
                    if "error" not in plan:
                        st.success(f"Route: {' → '.join(plan['route_order'])}")
                        c1, c2, c3 = st.columns(3)
                        c1.metric("Total km",   f'{plan["total_km"]} km')
                        c2.metric("Total ETA",  f'{plan["total_eta_min"]} min')
                        c3.metric("CO₂ Saved",  f'{plan["total_co2_kg"]:.3f} kg')
                    else:
                        st.error(plan["error"])

            # ── Tab: Demand Bubbles ───────────────────────────────────────────────
            with t_bubble:
                st.markdown("### 🫧 Zone Demand Bubble Map")
                st.caption(
                    "Bubble radius and brightness ∝ weighted demand index "
                    "(avg 7-day forecast × live price × zone variance). "
                    "Click a bubble for the per-SKU breakdown."
                )
                fc_map = fcs if fcs else {
                    i.get("sku_id", ""): {"forecast": [50] * FORECAST_DAYS} for i in inv
                }
                bubble_folium_m = self.maps.render_demand_bubbles(inv, fc_map, prices)
                if bubble_folium_m is not None:
                    st_folium(
                        bubble_folium_m,
                        width            = "100%",
                        height           = 520,
                        returned_objects = [],
                        key              = "bubble_map",
                    )

            # ── Tab: Riders & Revenue ─────────────────────────────────────────────
            with t_rider:
                rt_rider, rt_revenue = st.tabs(["🏍️ Rider Distribution", "📊 Zone Revenue"])

                with rt_rider:
                    st.markdown("### 🏍️ Rider Distribution Map")
                    st.caption("Circle size ∝ order count per delivery zone.")
                    orders = self.db.get_recent_orders(limit=120)
                    rider_folium_m = self.maps.render_rider_map(orders)
                    if rider_folium_m is not None:
                        st_folium(
                            rider_folium_m,
                            width            = "100%",
                            height           = 500,
                            returned_objects = [],
                            key              = "rider_map",
                        )

                with rt_revenue:
                    st.markdown("### 📊 Zone Revenue Map")
                    st.caption("Colour and size ∝ total revenue per zone (brighter = higher).")
                    zone_stats = self.db.get_zone_stats()
                    if zone_stats:
                        rev_folium_m = self.maps.render_zone_revenue(zone_stats)
                        if rev_folium_m is not None:
                            st_folium(
                                rev_folium_m,
                                width            = "100%",
                                height           = 500,
                                returned_objects = [],
                                key              = "revenue_map",
                            )
                    else:
                        st.info("No order data yet — place some orders to see the revenue map.")
    # ═════════════════════════════════════════════════════════════════════════
    # TAB 5 — LOGISTICS
    # ═════════════════════════════════════════════════════════════════════════

    def _t5_logistics(self, inv: List[Dict], prices: Dict) -> None:
        st.markdown("## 🚚 Logistics & Order Management")
        t_ord, t_new, t_carbon = st.tabs(["📋 Orders","➕ New Order","🌱 Carbon Ledger"])

        with t_ord:
            st.markdown("### Recent Orders")
            orders = self.db.get_recent_orders(limit=50)
            stats  = self.db.get_order_stats()
            c1,c2,c3,c4,c5 = st.columns(5)
            c1.metric("Total",     stats.get("total",0))
            c2.metric("Delivered", stats.get("delivered",0))
            c3.metric("Transit",   stats.get("in_transit",0))
            c4.metric("Processing",stats.get("processing",0))
            c5.metric("Pending",   stats.get("pending",0))

            if PANDAS_AVAILABLE and orders:
                st.dataframe(pd.DataFrame([{
                    "ID": o["order_id"], "SKU": SKUS.get(o["sku_id"],("?",""))[0],
                    "Qty": o["quantity"], "Price৳": o["unit_price"],
                    "Zone": o.get("zone","?"), "Rider": o.get("rider_id","—"),
                    "Status": o["status"], "Created": o["created_at"][:16],
                } for o in orders]), use_container_width=True, height=360)
            else:
                for o in orders[:10]: st.write(o)

            st.divider()
            col_a1, col_a2 = st.columns(2)
            with col_a1:
                adv_id = st.number_input("Order ID to advance",min_value=1,value=1,key="adv_id")
                if st.button("⏩ Advance Status",key="adv_btn"):
                    new_s = self.business.advance_order_status(adv_id)
                    st.success(f"Order {adv_id} → {new_s}"); st.rerun()
            with col_a2:
                ass_id   = st.number_input("Order ID for rider",min_value=1,value=1,key="ass_id")
                ass_zone = st.selectbox("Zone",list(DHAKA_HUBS.keys()),key="ass_zone")
                if st.button("🏍️ Assign Rider",key="ass_btn"):
                    rider = self.business.assign_rider(ass_id, ass_zone)
                    st.success(f"Rider {rider} → Order {ass_id}"); st.rerun()

        with t_new:
            st.markdown("### ➕ Place New Order")
            sku_map = {i.get("sku_id",""): i.get("name","?") for i in inv}
            n1,n2,n3,n4 = st.columns(4)
            with n1: n_sku  = st.selectbox("SKU",list(sku_map.keys()),format_func=lambda x:sku_map.get(x,x),key="n_sku")
            with n2: n_qty  = st.number_input("Qty",min_value=1,max_value=200,value=2,key="n_qty")
            with n3: n_zone = st.selectbox("Zone",list(DHAKA_HUBS.keys()),key="n_zone")
            with n4: n_cid  = st.text_input("Customer ID",value="C9999",key="n_cid")

            item_  = next((i for i in inv if i.get("sku_id")==n_sku),{})
            base_p = prices.get(n_sku,{}).get("price", item_.get("unit_cost",100)) or 100
            dyn    = self.business.dynamic_price(
                n_sku, base_p,
                stock=item_.get("current_stock",50), eoq=item_.get("eoq",50),
                expiry=item_.get("expiry_days",30),
                event=st.session_state.get("market_event","Normal Day"),
            )
            adj_p = dyn["adjusted_price"]
            total = adj_p * n_qty
            src   = prices.get(n_sku,{}).get("data_source","?")

            st.info(f"Unit price (dynamic): ৳{adj_p}  |  Total: ৳{total:.2f}  |  Reason: {dyn['reason']}  |  Price source: {src}")

            if st.button("✅ Place Order",key="place_btn"):
                oid = self.db.place_order(n_sku, n_qty, adj_p, n_cid, n_zone)
                if oid:
                    self.db.execute_query(
                        "UPDATE inventory SET current_stock=MAX(0,current_stock-?) WHERE sku_id=?",
                        (n_qty, n_sku),
                    )
                    self.log_action(
                        "ORDER_PLACE",
                        f"Order #{oid}: {n_qty}× {sku_map.get(n_sku,'?')} → zone={n_zone} "
                        f"price=৳{adj_p} total=৳{total:.2f} customer={n_cid}",
                    )
                    st.success(f"Order #{oid}: {n_qty}× {sku_map.get(n_sku,'?')} → {n_zone}  ৳{total:.2f}")
                    st.rerun()

        with t_carbon:
            st.markdown("### 🌱 Carbon Savings Ledger")
            totals = self.db.get_carbon_total()
            c1,c2,c3,c4 = st.columns(4)
            c1.metric("Routes Logged",    totals.get("routes",0))
            c2.metric("Fuel Saved (L)",   f'{totals.get("fuel",0) or 0:.2f}')
            c3.metric("CO₂ Saved (kg)",   f'{totals.get("co2",0)  or 0:.3f}')
            c4.metric("Cost Saved (৳)",   f'{totals.get("cost",0) or 0:.0f}')

            carbon_rows = self.db.fetch_all(
                "SELECT route_id,traditional_km,optimal_km,co2_saved_kg,"
                "cost_saved_bdt,recorded_at FROM carbon_ledger ORDER BY recorded_at DESC LIMIT 30"
            )
            if carbon_rows and PANDAS_AVAILABLE:
                st.dataframe(pd.DataFrame(carbon_rows), use_container_width=True)
            else:
                st.info("Use the Route Planner to populate the carbon ledger.")

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 6 — FINANCE
    # ═════════════════════════════════════════════════════════════════════════

    def _t6_finance(self, inv: List[Dict], prices: Dict) -> None:
        st.markdown("## 💰 Financial Analytics")
        st.caption("Revenue data from real DB orders — no fabricated figures")

        summary = self.business.revenue_summary()
        skuperf = self.business.sku_performance(inv, prices)

        c1,c2,c3,c4 = st.columns(4)
        c1.metric("💵 Total Revenue",   f'৳{summary["total_revenue"]:,.0f}')
        c2.metric("📦 Inventory Value", f'৳{summary["inventory_value"]:,.0f}')
        c3.metric("✅ Delivered",        summary["delivered"])
        c4.metric("🏍️ In-Transit",       summary["in_transit"])

        st.divider()
        st.markdown("### 📅 Daily Revenue — Last 7 Days (from DB)")
        daily = summary.get("daily",[])
        if daily:
            rev_vals = [d["revenue"] for d in daily]
            if any(v > 0 for v in rev_vals):
                st.markdown(_spark_bar(rev_vals,"#00ff88",60), unsafe_allow_html=True)
            cols = st.columns(7)
            for col_, d in zip(cols, daily):
                col_.metric(d["day"], f'৳{int(d["revenue"]):,}', f'{d["order_count"]} orders')
        else:
            st.info("No orders in the last 7 days.")

        st.divider()
        st.markdown("### 📊 SKU Financial Performance")
        if skuperf and PANDAS_AVAILABLE:
            df = pd.DataFrame([{
                "SKU":        s["name"], "Category":   s["category"],
                "Sell৳":      s["sell_price"], "Cost৳": s["unit_cost"],
                "Margin%":    s["gross_margin"],
                "StockVal৳":  s["stock_value"], "PotGP৳": s["potential_gp"],
                "DataSrc":    s["data_source"],
            } for s in skuperf])
            st.dataframe(df, use_container_width=True, height=360)

        st.divider()
        st.markdown("### 🌿 Environmental Impact Summary")
        ct     = self.db.get_carbon_total()
        trees  = round((ct.get("co2",0) or 0) / 22, 2)
        c1,c2,c3 = st.columns(3)
        c1.metric("🌱 CO₂ Offset (kg)",  f'{ct.get("co2",0) or 0:.3f}')
        c2.metric("🌳 Tree Equivalent",   f'{trees}')
        c3.metric("💸 Fuel Cost Saved ৳", f'{ct.get("cost",0) or 0:.0f}')

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 7 — ALERTS
    # ═════════════════════════════════════════════════════════════════════════

    def _t7_alerts(self) -> None:
        st.markdown("## 🔔 System Alerts")
        alerts = self.db.get_unacknowledged_alerts()
        counts = self.db.get_alert_count()

        c1,c2,c3 = st.columns(3)
        c1.metric("🔴 Critical", counts.get("critical",0))
        c2.metric("🟡 Warning",  counts.get("warning",0))
        c3.metric("🔵 Info",     counts.get("info",0))

        col_a, col_b = st.columns(2)
        with col_a:
            if st.button("✅ Acknowledge All",key="ack_all"):
                self.db.acknowledge_all_alerts()
                st.success("All acknowledged."); st.rerun()
        with col_b:
            if st.button("🤖 Auto-Detect New Alerts",key="auto_detect"):
                prices  = self.scraper.fetch_chaldal_prices()
                weather = self.scraper.fetch_weather_data()
                inv     = self.db.get_inventory()
                n = self.business.auto_generate_alerts(inv, prices, weather)
                st.success(f"Generated {n} alert(s)"); st.rerun()

        st.divider()
        if not alerts:
            st.success("✅ No unacknowledged alerts — system nominal.")
        else:
            for alert in alerts:
                sev = alert.get("severity","info")
                msg = alert.get("message","")
                cat = alert.get("category","")
                aid = alert.get("id")
                ts  = alert.get("created_at","")[:16]
                cola, colb = st.columns([5,1])
                with cola:
                    if sev == "critical": st.error(f"🚨 [{cat}] {msg}  ·  {ts}")
                    elif sev == "warning": st.warning(f"⚠️ [{cat}] {msg}  ·  {ts}")
                    else: st.info(f"ℹ️ [{cat}] {msg}  ·  {ts}")
                with colb:
                    if st.button("✓",key=f"ack_{aid}"):
                        self.db.acknowledge_alert(aid); st.rerun()

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 8 — AI LOGS
    # ═════════════════════════════════════════════════════════════════════════

    def _t8_ai_logs(self) -> None:
        st.markdown("## 📋 AI Audit Trail")
        logs     = self.db.get_ai_logs(limit=30)
        dss_hist = self.db.get_dss_history(limit=30)

        cl, cd = st.columns(2)
        with cl:
            st.markdown("### 🤖 LLM Call Log")
            if logs and PANDAS_AVAILABLE:
                st.dataframe(pd.DataFrame([{
                    "Event": l.get("event_type",""), "SKU": l.get("sku_id","all"),
                    "Model": l.get("model_used","")[:22], "Tokens": l.get("tokens_used",0),
                    "Time":  l.get("created_at","")[:16],
                } for l in logs]), use_container_width=True, height=350)
            else: st.info("No AI logs yet.")

        with cd:
            st.markdown("### ⚖️ DSS Score History")
            if dss_hist and PANDAS_AVAILABLE:
                st.dataframe(pd.DataFrame([{
                    "SKU":    SKUS.get(d.get("sku_id",""),("?",""))[0],
                    "Score":  f'{d.get("total_score",0):.3f}',
                    "Action": d.get("action",""),
                    "Time":   d.get("scored_at","")[:16],
                } for d in dss_hist]), use_container_width=True, height=350)
            else: st.info("Run DSS engine and save scores.")

    # ═════════════════════════════════════════════════════════════════════════
    # TAB 9 — SETTINGS
    # ═════════════════════════════════════════════════════════════════════════

    def _t9_settings(self, inv: List[Dict], prices: Dict, fcs: Dict) -> None:
        st.markdown("## ⚙️ System Settings & Configuration")
        tw, tdb, tinfo, taudit, tusers = st.tabs([
            "⚖️ DSS Weights", "🗄️ Database", "ℹ️ System Info",
            "📋 Audit Logs", "👥 User Management",
        ])

        with tw:
            st.markdown("### MCDA Weight Calibration (must sum to 1.0)")
            w = self.dss.weights
            c1,c2,c3,c4,c5 = st.columns(5)
            w1 = c1.slider("Demand", 0.0,1.0,float(w.get("demand_score",0.30)),0.05,key="w1")
            w2 = c2.slider("Price",  0.0,1.0,float(w.get("price_score",0.20)), 0.05,key="w2")
            w3 = c3.slider("Stock",  0.0,1.0,float(w.get("stock_score",0.25)), 0.05,key="w3")
            w4 = c4.slider("Expiry", 0.0,1.0,float(w.get("expiry_score",0.15)),0.05,key="w4")
            w5 = c5.slider("Margin", 0.0,1.0,float(w.get("margin_score",0.10)),0.05,key="w5")
            tot = round(w1+w2+w3+w4+w5,2)
            if abs(tot-1.0) < 0.02: st.success(f"✅ Weights valid (sum = {tot})")
            else:                   st.error(f"❌ Sum = {tot} — must be 1.0")

            bw1,bw2 = st.columns(2)
            with bw1:
                if st.button("💾 Save Weights",key="sv_w"):
                    ok = self.dss.update_weights({"demand_score":w1,"price_score":w2,"stock_score":w3,"expiry_score":w4,"margin_score":w5})
                    if ok: st.success("Saved.")
                    else:  st.error("Sum ≠ 1.0 — not saved.")
            with bw2:
                if st.button("↩️ Reset Defaults",key="rst_w"):
                    self.dss.weights = DEFAULT_DSS_WEIGHTS.copy()
                    st.success("Reset."); st.rerun()

        with tdb:
            st.markdown("### Data Exports")
            # ── FIX: download_buttons are always rendered (not in button blocks) ──
            inv_json  = json.dumps(inv,  indent=2, default=str)
            ords      = self.db.get_recent_orders(200)
            ords_json = json.dumps(ords, indent=2, default=str)

            col_e1, col_e2 = st.columns(2)
            with col_e1:
                st.markdown("**Inventory Export**")
                st.download_button(
                    label="⬇️ Download inventory.json",
                    data=inv_json.encode("utf-8"),
                    file_name=f"inventory_{datetime.date.today()}.json",
                    mime="application/json",
                    key="dl_inv",
                )
            with col_e2:
                st.markdown("**Orders Export**")
                st.download_button(
                    label="⬇️ Download orders.json",
                    data=ords_json.encode("utf-8"),
                    file_name=f"orders_{datetime.date.today()}.json",
                    mime="application/json",
                    key="dl_ords",
                )

            st.divider()

            # CSV export
            if PANDAS_AVAILABLE and inv:
                csv_buf = io.StringIO()
                pd.DataFrame(inv).to_csv(csv_buf, index=False)
                st.download_button(
                    label="⬇️ Download inventory.csv",
                    data=csv_buf.getvalue().encode("utf-8"),
                    file_name=f"inventory_{datetime.date.today()}.csv",
                    mime="text/csv",
                    key="dl_inv_csv",
                )

            st.divider()
            st.markdown("### Database Controls")
            cc1, cc2 = st.columns(2)
            with cc1:
                if st.button("🧹 Acknowledge All Alerts",key="ack_all_s"):
                    self.db.acknowledge_all_alerts(); st.success("Done.")
            with cc2:
                if st.button("🗑️ Clear Carbon Ledger",key="clr_c"):
                    self.db.execute_query("DELETE FROM carbon_ledger"); st.success("Cleared.")

            st.divider()
            st.markdown("### Raw SQL Query (SELECT only)")
            sql_in = st.text_area("SQL","SELECT * FROM inventory LIMIT 5",key="raw_sql")
            if st.button("▶️ Execute",key="raw_btn"):
                if sql_in.strip().upper().startswith("SELECT"):
                    rows = self.db.fetch_all(sql_in)
                    if rows and PANDAS_AVAILABLE: st.dataframe(pd.DataFrame(rows), use_container_width=True)
                    else: st.write(rows)
                else: st.error("Only SELECT statements allowed.")

        with tinfo:
            st.markdown("### System Information")

            # Determine LSTM status string without apostrophe in f-string
            lstm_status = "Yes (TensorFlow)" if TF_AVAILABLE else "No (Holts stats fallback)"
            llm_status  = "Active" if self.soptom.is_llm_active() else "No (rule-based)"
            nx_status   = "Yes" if NX_AVAILABLE else "No (Haversine fallback)"
            pd_status   = "Yes" if PANDAS_AVAILABLE else "No"
            bs4_status  = "Yes" if BS4_AVAILABLE else "No (scraping disabled)"
            sdk_status  = "openai SDK" if OPENAI_SDK else ("groq SDK" if GROQ_SDK else "None")
            pydeck_status   = "Yes" if PYDECK_AVAILABLE else "No (pip install pydeck)"
            polyline_status = "Yes" if POLYLINE_AVAILABLE else "No (pip install polyline)"
            geopandas_status = "Yes" if GEOPANDAS_AVAILABLE else "No (pip install geopandas)"

            st.markdown(
                f'<div class="nx-card"><h4>🔧 Runtime</h4><p>'
                f'App: <b>{APP_NAME} v{APP_VERSION}</b><br>'
                f'Developer: <b>{DEVELOPER}</b><br>'
                f'Database: <b>{DB_PATH}</b><br>'
                f'AI Model: <b>{self.soptom.get_model_name()}</b><br>'
                f'LLM SDK: <b>{sdk_status}</b><br>'
                f'LLM Active: <b>{llm_status}</b><br>'
                f'LSTM: <b>{lstm_status}</b><br>'
                f'NetworkX: <b>{nx_status}</b><br>'
                f'Pandas: <b>{pd_status}</b><br>'
                f'BS4 Scraper: <b>{bs4_status}</b><br>'
                f'PyDeck (3D maps): <b>{pydeck_status}</b><br>'
                f'Polyline (OSRM): <b>{polyline_status}</b><br>'
                f'GeoPandas (PIP): <b>{geopandas_status}</b><br>'
                f'Grok API Key: <b>{"Set" if GROK_API_KEY else "Missing"}</b><br>'
                f'Scrape TTL: <b>{SCRAPE_TTL}s</b><br>'
                f'Forecast Horizon: <b>{FORECAST_DAYS} days</b>'
                f'</p></div>',
                unsafe_allow_html=True,
            )

            st.markdown("### Data Source Status")
            src_label = self.scraper.get_data_source_label()
            st.markdown(f"**Current price data:** {src_label}")
            st.info(
                "Scraping hierarchy:\n"
                "1. Chaldal Category API (POST)\n"
                "2. Chaldal Search API (GET per SKU)\n"
                "3. __NEXT_DATA__ HTML scrape\n"
                "4. Last-known-good cache\n"
                "5. Reference prices (static baseline — labelled 🔴 REF)"
            )

            if PANDAS_AVAILABLE:
                st.markdown("### SKU Catalogue")
                st.dataframe(pd.DataFrame(
                    [{"sku_id":k,"name":v[0],"category":v[1]} for k,v in SKUS.items()]
                ), use_container_width=True)

                st.markdown("### Hub Network")
                st.dataframe(pd.DataFrame(
                    [{"hub":h,"lat":c[0],"lon":c[1]} for h,c in DHAKA_HUBS.items()]
                ), use_container_width=True)

            # ── Zone Analyzer section ─────────────────────────────────────────
            st.divider()
            st.markdown("### 🗺️ GIS Zone Analyzer (Point-in-Polygon)")
            if self.zones:
                st.markdown(self.zones.zone_summary())
                st.markdown("**Test PIP lookup:**")
                pip_col1, pip_col2 = st.columns(2)
                with pip_col1:
                    test_lat = st.number_input("Latitude",  value=23.775, format="%.4f", key="pip_lat")
                    test_lon = st.number_input("Longitude", value=90.408, format="%.4f", key="pip_lon")
                if st.button("🔍 Find Zone", key="pip_btn"):
                    zone_hit = self.zones.get_zone(test_lat, test_lon)
                    hub_hit  = self.zones.assign_nearest_hub(test_lat, test_lon)
                    if zone_hit:
                        st.success(f"📍 Point ({test_lat:.4f}, {test_lon:.4f}) is in **{zone_hit}** zone → assigned hub: **{hub_hit}**")
                    else:
                        st.warning(f"⚠️ Point outside polygon zones. Nearest hub (Haversine): **{hub_hit}**")
            else:
                st.info("ZoneAnalyzer not initialised.")

        # ── Audit Logs Tab ────────────────────────────────────────────────────
        with taudit:
            st.markdown("### 📋 Audit Trail")

            is_admin_view = self.auth.is_admin() if self.auth else True
            if not is_admin_view:
                st.warning("🔒 Audit logs are visible to **admin** users only.")
            else:
                limit_opt = st.slider("Rows to show", 10, 200, 50, key="audit_limit")
                logs = self.db.get_audit_logs(limit=limit_opt)
                if logs and PANDAS_AVAILABLE:
                    df = pd.DataFrame(logs)
                    # Colour-code action types
                    def _row_colour(t: str) -> str:
                        if "FAIL" in t:   return "🔴"
                        if "LOGIN" in t:  return "🟢"
                        if "LOGOUT" in t: return "🟡"
                        if "CLOSE" in t:  return "🔴"
                        return "⚪"
                    df["icon"] = df["action_type"].apply(_row_colour)
                    df = df[["icon","timestamp","username","role","action_type","description"]]
                    df.columns = ["","Time","User","Role","Action","Description"]
                    st.dataframe(df, use_container_width=True, height=420)
                elif logs:
                    for row in logs:
                        st.write(row)
                else:
                    st.info("No audit log entries yet. Actions like Login, Place Order, and Update Stock are recorded here.")

                if st.button("🗑️ Clear Audit Logs (Admin Only)", key="clr_audit"):
                    self.db.execute_query("DELETE FROM audit_logs")
                    self.log_action("AUDIT_CLEAR", "Admin cleared the entire audit log.")
                    st.success("Audit log cleared.")
                    st.rerun()

        # ── User Management Tab ───────────────────────────────────────────────
        with tusers:
            st.markdown("### 👥 User Management")

            is_admin_mgmt = self.auth.is_admin() if self.auth else True
            if not is_admin_mgmt:
                st.warning("🔒 User management is restricted to **admin** users only.")
            else:
                # ── Current users table ───────────────────────────────────────
                st.markdown("#### Active Users")
                users = self.db.list_users()
                if users and PANDAS_AVAILABLE:
                    st.dataframe(pd.DataFrame(users), use_container_width=True, height=200)
                else:
                    for u in users: st.write(u)

                st.divider()

                # ── Create new user ───────────────────────────────────────────
                st.markdown("#### ➕ Create New User")
                nc1, nc2 = st.columns(2)
                with nc1:
                    nu_uname = st.text_input("Username",   key="nu_uname", placeholder="e.g. jdoe")
                    nu_name  = st.text_input("Full Name",  key="nu_name",  placeholder="e.g. John Doe")
                    nu_email = st.text_input("Email",      key="nu_email", placeholder="jdoe@logix.bd")
                with nc2:
                    nu_role  = st.selectbox("Role", list(ROLE_TAB_ACCESS.keys()), key="nu_role")
                    nu_pass  = st.text_input("Password",   key="nu_pass",  type="password")
                    nu_pass2 = st.text_input("Confirm Pwd",key="nu_pass2", type="password")

                if st.button("✅ Create User", key="nu_btn"):
                    if not all([nu_uname, nu_name, nu_email, nu_pass]):
                        st.error("All fields are required.")
                    elif nu_pass != nu_pass2:
                        st.error("Passwords do not match.")
                    elif len(nu_pass) < 8:
                        st.error("Password must be at least 8 characters.")
                    else:
                        ok = self.db.create_user(nu_uname.lower(), nu_email, nu_name, nu_pass, nu_role)
                        if ok:
                            self.log_action("USER_CREATE",
                                f"New user '{nu_uname}' (role={nu_role}) created.")
                            st.success(f"User **{nu_uname}** created successfully.")
                            st.rerun()
                        else:
                            st.error(f"Username or email already exists.")

                st.divider()

                # ── Change password ───────────────────────────────────────────
                st.markdown("#### 🔑 Change Password")
                cp1, cp2 = st.columns(2)
                with cp1:
                    cp_user = st.selectbox(
                        "User", [u["username"] for u in users], key="cp_user"
                    )
                with cp2:
                    cp_new  = st.text_input("New Password", key="cp_new", type="password")

                if st.button("💾 Update Password", key="cp_btn"):
                    if len(cp_new) < 8:
                        st.error("Password must be at least 8 characters.")
                    else:
                        ok = self.db.change_password(cp_user, cp_new)
                        if ok:
                            self.log_action("USER_PWD_CHANGE",
                                f"Password changed for user '{cp_user}'.")
                            st.success(f"Password updated for **{cp_user}**.")
                        else:
                            st.error("Update failed.")

                st.divider()

                # ── Deactivate user ───────────────────────────────────────────
                st.markdown("#### 🚫 Deactivate User")
                active_users = [u["username"] for u in users if u.get("is_active") == 1]
                deact_user = st.selectbox("User to deactivate", active_users, key="deact_user")
                if st.button("🚫 Deactivate", key="deact_btn"):
                    current_uname = self.auth.current_user().get("username") if self.auth else ""
                    if deact_user == current_uname:
                        st.error("You cannot deactivate your own account.")
                    else:
                        self.db.deactivate_user(deact_user)
                        self.log_action("USER_DEACTIVATE",
                            f"User '{deact_user}' deactivated.")
                        st.success(f"User **{deact_user}** deactivated.")
                        st.rerun()


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 8 ── MASTER CONTROLLER
# ═══════════════════════════════════════════════════════════════════════════════


# ── Memory-efficient singleton factories using st.cache_resource ─────────────
# cache_resource stores ONE instance per process (not per session), which
# dramatically reduces RAM usage compared to session_state-per-user storage.

@st.cache_resource(show_spinner=False)
def _get_db_singleton() -> NexusDatabase:
    logging.getLogger("LogixApp").info("Init NexusDatabase (cache_resource)")
    return NexusDatabase(DB_PATH)

@st.cache_resource(show_spinner=False)
def _get_scraper_singleton() -> LiveDataScraper:
    logging.getLogger("LogixApp").info("Init LiveDataScraper (cache_resource)")
    return LiveDataScraper()

@st.cache_resource(show_spinner=False)
def _get_soptom_singleton() -> "SoptomAlgorithm":
    logging.getLogger("LogixApp").info("Init SoptomAlgorithm (cache_resource)")
    return SoptomAlgorithm(db=_get_db_singleton())

@st.cache_resource(show_spinner=False)
def _get_dss_singleton() -> DSSEngine:
    return DSSEngine()

@st.cache_resource(show_spinner=False)
def _get_business_singleton() -> BusinessEngine:
    return BusinessEngine(_get_db_singleton())

@st.cache_resource(show_spinner=False)
def _get_routing_singleton() -> RoutingEngine:
    return RoutingEngine()

@st.cache_resource(show_spinner=False)
def _get_maps_singleton() -> MapRenderer:
    return MapRenderer()

@st.cache_resource(show_spinner=False)
def _get_pydeck_singleton() -> PyDeckRenderer:
    return PyDeckRenderer()

@st.cache_resource(show_spinner=False)
def _get_zones_singleton() -> ZoneAnalyzer:
    return ZoneAnalyzer()

@st.cache_resource(show_spinner=False)
def _get_auth_singleton() -> AuthManager:
    return AuthManager(db=_get_db_singleton())

@st.cache_resource(show_spinner=False)
def _get_ui_singleton() -> "NexusUI":
    return NexusUI(
        db       = _get_db_singleton(),
        scraper  = _get_scraper_singleton(),
        soptom   = _get_soptom_singleton(),
        dss      = _get_dss_singleton(),
        business = _get_business_singleton(),
        routing  = _get_routing_singleton(),
        maps     = _get_maps_singleton(),
        pydeck   = _get_pydeck_singleton(),
        zones    = _get_zones_singleton(),
        auth     = _get_auth_singleton(),
    )


class ApplicationController:
    """
    Application orchestrator.
    Heavy objects are built once per process via @st.cache_resource
    (not per session), massively reducing RAM usage on Streamlit Cloud.
    """

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)

    def start(self) -> None:
        try:
            self._init_defaults()
            _get_ui_singleton().render()
        except Exception as exc:
            self._error_page(exc)

    def _init_defaults(self) -> None:
        for key, val in {
            "market_event": "Normal Day",
            "forecasts":    {},
            "last_route":   None,
            "proc_plan":    None,
            "dss_sens":     None,
        }.items():
            if key not in st.session_state:
                st.session_state[key] = val

    def _error_page(self, exc: Exception) -> None:
        tb = traceback.format_exc()
        self.logger.critical("Fatal: %s\n%s", exc, tb)
        # এটি আপনাকে কোডের ভুলটি সরাসরি স্ক্রিনে দেখতে সাহায্য করবে
        st.markdown(
            f"""<div style="background:#1a0a0a;border:2px solid #ff3366;border-radius:14px;
                            padding:2rem;margin:2rem auto;max-width:900px;">
              <h2 style="color:#ff3366;">🚀 LOGIX — Fatal Error</h2>
              <p style="color:#ffbbbb;"><b>{type(exc).__name__}:</b> {exc}</p>
              <pre style="color:#ffcccc;font-size:.78rem;overflow:auto;">{tb}</pre>
            </div>""",
            unsafe_allow_html=True,
        )


# ═══════════════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════════

def main() -> None:
    """
    LOGIX v7.0 — Production Supply Chain Intelligence Platform.
    Developer: Sourab Dey Soptom
    Run: streamlit run logix_v7.py
    """
    ApplicationController().start()


if __name__ == "__main__":
    main()
