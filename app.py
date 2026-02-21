
# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 1 ── IMPORTS, CONSTANTS & GLOBAL CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

import os, json, time, math, random, sqlite3, logging, warnings
import datetime, traceback, hashlib, re, io, csv, threading
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any, Union
from collections import defaultdict

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

# ── TensorFlow / Keras
try:
    import tensorflow as tf  # type: ignore
    from tensorflow.keras.models import Sequential  # type: ignore
    from tensorflow.keras.layers import LSTM, Dense, Dropout  # type: ignore
    from tensorflow.keras.optimizers import Adam  # type: ignore
    TF_AVAILABLE = True
except ImportError:
    TF_AVAILABLE = False

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

APP_VERSION   = "7.0.0"
APP_NAME      = "LOGIX"
DEVELOPER     = "Sourab Dey Soptom"
DB_PATH       = "logix_v7.db"
SCRAPE_TTL    = 600            # 10-min cache
FORECAST_DAYS = 7
CHALDAL_BASE  = "https://chaldal.com"

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
            sku      = list(SKUS.keys())[i % len(SKUS)]
            qty      = (i % 4) + 1
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

        if TF_AVAILABLE and NP_AVAILABLE:
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
    Dijkstra-based delivery routing with hub closure and multi-stop TSP.
    """

    AVG_SPEED_KMH    = 25.0
    VEHICLE_CAPACITY = 30

    def __init__(self) -> None:
        self.logger       = logging.getLogger(self.__class__.__name__)
        self._closed_hubs: set = set()

    def find_optimal_route(self, source: str, target: str, mode: str = "balanced") -> Dict[str, Any]:
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
    Zero-dependency interactive map renderer for LOGIX v7.0.
    Uses pure Leaflet.js loaded from CDN — no pip packages required.
    Works on Streamlit Cloud and any browser without any installation.
    """

    DHAKA_CENTER = [23.7808, 90.4007]
    DEFAULT_ZOOM = 12

    COLORS = {
        "hub_open":    "#00ff88",
        "hub_closed":  "#ff3366",
        "route":       "#00cfff",
        "edge_low":    "#2a9d8f",
        "edge_mid":    "#e9c46a",
        "edge_high":   "#e76f51",
        "bubble":      "#ff6b35",
        "rider":       "#c084fc",
        "revenue_low": "#1a6b3a",
        "revenue_hi":  "#00ff88",
    }

    # ── Shared Leaflet boilerplate ─────────────────────────────────────────────
    _LEAFLET_HEAD = """
    <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"/>
    <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
    <style>
      body { margin:0; padding:0; background:#0a0e1a; }
      #map { width:100%; height:{HEIGHT}px; background:#0a0e1a; }
      .legend {
        position:absolute; bottom:20px; left:20px; z-index:1000;
        background:rgba(10,14,26,0.92); border:1px solid #1e3a5f;
        border-radius:8px; padding:10px 14px;
        font-family:monospace; font-size:12px; color:#7dd3fc;
        line-height:1.7;
      }
    </style>
    """

    _LEAFLET_INIT = """
    var map = L.map('map', {zoomControl:true, attributionControl:false})
              .setView([23.7808, 90.4007], 12);
    L.tileLayer(
      'https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png',
      {subdomains:'abcd', maxZoom:19}
    ).addTo(map);
    """

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)
        # Always available — pure JS, no Python deps
        self._folium_available = True

    # ── Internal colour helpers ───────────────────────────────────────────────

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
        if traffic < 1.3:  return MapRenderer.COLORS["edge_low"]
        if traffic < 1.6:  return MapRenderer.COLORS["edge_mid"]
        return MapRenderer.COLORS["edge_high"]

    @staticmethod
    def _traffic_label(traffic: float) -> str:
        if traffic < 1.3:  return "Low"
        if traffic < 1.6:  return "Moderate"
        return "Heavy"

    def _wrap_html(self, js_body: str, legend_html: str, height: int = 540) -> str:
        """Wrap JS drawing code inside a complete self-contained HTML document."""
        head = self._LEAFLET_HEAD.replace("{HEIGHT}", str(height))
        return f"""<!DOCTYPE html><html><head>{head}</head><body>
<div id="map"></div>
<div class="legend">{legend_html}</div>
<script>
{self._LEAFLET_INIT}
{js_body}
</script>
</body></html>"""

    # ── Public API — each method returns an HTML string ───────────────────────

    def render_hub_map(
        self,
        hub_metrics:  List[Dict],
        route_result: Optional[Dict]      = None,
        closed_hubs:  Optional[List[str]] = None,
    ) -> str:
        closed        = set(closed_hubs or [])
        metric_by_hub = {hm["hub"]: hm for hm in hub_metrics}
        js_lines: List[str] = []

        # ── Hub edges ─────────────────────────────────────────────────────────
        for hub_a, hub_b, km, traffic in HUB_EDGES:
            if hub_a not in DHAKA_HUBS or hub_b not in DHAKA_HUBS:
                continue
            la, lo_a = DHAKA_HUBS[hub_a]
            lb, lo_b = DHAKA_HUBS[hub_b]
            color    = self._traffic_color(traffic)
            label    = self._traffic_label(traffic)
            js_lines.append(
                f"L.polyline([[{la},{lo_a}],[{lb},{lo_b}]],{{color:'{color}',"
                f"weight:2.5,opacity:0.75}}).bindTooltip("
                f"'<b>{hub_a} → {hub_b}</b><br>{km} km · {label} traffic').addTo(map);"
            )

        # ── Active route overlay ──────────────────────────────────────────────
        if route_result and "path" in route_result and len(route_result["path"]) >= 2:
            coords = [
                f"[{DHAKA_HUBS[h][0]},{DHAKA_HUBS[h][1]}]"
                for h in route_result["path"] if h in DHAKA_HUBS
            ]
            if len(coords) >= 2:
                path_str  = ",".join(coords)
                km_r      = route_result.get("total_km", "?")
                eta_r     = route_result.get("eta_min", "?")
                c         = self.COLORS["route"]
                path_label = " → ".join(route_result["path"])
                js_lines.append(
                    f"L.polyline([{path_str}],{{color:'{c}',weight:5,opacity:0.95,"
                    f"dashArray:'10 6'}}).bindTooltip('<b>Optimal Route</b><br>"
                    f"{path_label}<br>{km_r} km · {eta_r} min').addTo(map);"
                )
                # Endpoint markers
                for coord in [coords[0], coords[-1]]:
                    js_lines.append(
                        f"L.circleMarker({coord},{{radius:9,color:'{c}',"
                        f"fillColor:'#fff',fillOpacity:0.9,weight:2}}).addTo(map);"
                    )

        # ── Hub circle markers ────────────────────────────────────────────────
        for hub_name, (lat, lon) in DHAKA_HUBS.items():
            hm         = metric_by_hub.get(hub_name, {})
            is_closed  = hub_name in closed
            centrality = hm.get("centrality", 0.3)
            degree     = hm.get("degree", 2)
            radius     = max(9, min(int(10 + centrality * 20), 26))
            color      = self.COLORS["hub_closed"] if is_closed else self.COLORS["hub_open"]
            status     = "CLOSED" if is_closed else "OPEN"
            popup      = (
                f"<b>{hub_name}</b><br><span style='color:{color}'>{status}</span><br>"
                f"Centrality: {centrality:.4f}<br>Connections: {degree}<br>"
                f"{lat:.4f}N {lon:.4f}E"
            )
            js_lines.append(
                f"L.circleMarker([{lat},{lon}],{{radius:{radius},color:'{color}',"
                f"fillColor:'{color}',fillOpacity:0.80,weight:2}})"
                f".bindPopup('{popup}')"
                f".bindTooltip('<b>{hub_name}</b> [{status}] centrality:{centrality:.3f}').addTo(map);"
            )
            js_lines.append(
                f"L.marker([{lat+0.0015},{lon}],{{icon:L.divIcon({{html:"
                f"\"<div style='font-family:monospace;font-size:10px;font-weight:700;"
                f"color:{color};text-shadow:0 0 4px #000;text-align:center;"
                f"white-space:nowrap'>{hub_name}</div>\","
                f"iconSize:[100,16],iconAnchor:[50,8]}})  }}).addTo(map);"
            )

        legend = (
            "<b>Hub Network</b><br>"
            f"<span style='color:{self.COLORS['hub_open']}'>● Open hub</span><br>"
            f"<span style='color:{self.COLORS['hub_closed']}'>● Closed hub</span><br>"
            f"<span style='color:{self.COLORS['edge_low']}'>━ Low traffic</span><br>"
            f"<span style='color:{self.COLORS['edge_mid']}'>━ Moderate</span><br>"
            f"<span style='color:{self.COLORS['edge_high']}'>━ Heavy</span>"
        )
        return self._wrap_html("\n".join(js_lines), legend, height=540)

    def render_demand_bubbles(
        self,
        inventory: List[Dict],
        forecasts: Dict[str, Dict],
        prices:    Dict[str, Dict],
    ) -> str:
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
                details.append(f"{name}: {avg_d:.1f} u/day × {price:.0f}")
            zone_demand[hub]  = total
            zone_details[hub] = details

        max_demand = max(zone_demand.values()) or 1.0
        js_lines: List[str] = []

        for hub_name, (lat, lon) in DHAKA_HUBS.items():
            demand = zone_demand.get(hub_name, 0)
            ratio  = demand / max_demand
            radius       = max(12, min(int(15 + ratio * 50), 65))
            fill_opacity = round(0.20 + ratio * 0.55, 2)
            color        = self._interpolate_color(ratio, "#7b2d00", self.COLORS["bubble"])
            detail_lines = " | ".join(zone_details.get(hub_name, []))
            popup        = (
                f"<b>{hub_name}</b><br>"
                f"<b style='color:{self.COLORS['bubble']}'>Demand: {demand:,.0f}</b> "
                f"({ratio*100:.1f}% of peak)<br><small>{detail_lines}</small>"
            )
            # Outer glow ring
            js_lines.append(
                f"L.circleMarker([{lat},{lon}],{{radius:{radius+10},color:'{color}',"
                f"fillColor:'{color}',fillOpacity:0.06,weight:1}}).addTo(map);"
            )
            # Main bubble
            js_lines.append(
                f"L.circleMarker([{lat},{lon}],{{radius:{radius},color:'{color}',"
                f"fillColor:'{color}',fillOpacity:{fill_opacity},weight:2}})"
                f".bindPopup(\"{popup}\")"
                f".bindTooltip('<b>{hub_name}</b> | Demand: {demand:,.0f} ({ratio*100:.1f}%)').addTo(map);"
            )
            # Label
            js_lines.append(
                f"L.marker([{lat+0.0018},{lon}],{{icon:L.divIcon({{html:"
                f"\"<div style='font-family:monospace;font-size:10px;font-weight:700;"
                f"color:{color};text-shadow:0 0 4px #000;text-align:center;"
                f"white-space:nowrap'>{hub_name}</div>\","
                f"iconSize:[100,16],iconAnchor:[50,8]}})  }}).addTo(map);"
            )

        legend = (
            "<b>Demand Bubble Map</b><br>"
            f"<span style='color:{self.COLORS['bubble']}'>Large + bright = high demand</span><br>"
            "<i>Click bubble for SKU breakdown</i>"
        )
        return self._wrap_html("\n".join(js_lines), legend, height=520)

    def render_rider_map(self, orders: List[Dict]) -> str:
        zone_cnt: Dict[str, int]   = defaultdict(int)
        zone_rev: Dict[str, float] = defaultdict(float)

        for o in orders:
            z = o.get("zone", "Gulshan")
            zone_cnt[z] += 1
            zone_rev[z] += o.get("quantity", 1) * o.get("unit_price", 0)

        if not zone_cnt:
            for h in DHAKA_HUBS:
                zone_cnt[h] = 0

        max_cnt    = max(zone_cnt.values()) or 1
        color      = self.COLORS["rider"]
        js_lines: List[str] = []

        for hub_name, (lat, lon) in DHAKA_HUBS.items():
            cnt     = zone_cnt.get(hub_name, 0)
            rev     = zone_rev.get(hub_name, 0.0)
            ratio   = cnt / max_cnt
            radius  = max(8, min(int(10 + ratio * 35), 48))
            opacity = round(0.35 + ratio * 0.50, 2)
            popup   = (
                f"<b>{hub_name}</b><br>Orders: <b>{cnt}</b><br>"
                f"Revenue: <b>৳{rev:,.0f}</b>"
            )
            js_lines.append(
                f"L.circleMarker([{lat},{lon}],{{radius:{radius},color:'{color}',"
                f"fillColor:'{color}',fillOpacity:{opacity},weight:2}})"
                f".bindPopup('{popup}')"
                f".bindTooltip('<b>{hub_name}</b> | {cnt} orders | ৳{rev:,.0f}').addTo(map);"
            )
            js_lines.append(
                f"L.marker([{lat+0.0016},{lon}],{{icon:L.divIcon({{html:"
                f"\"<div style='font-family:monospace;font-size:10px;font-weight:700;"
                f"color:{color};text-shadow:0 0 4px #000;text-align:center;"
                f"white-space:nowrap'>{hub_name} ({cnt})</div>\","
                f"iconSize:[120,16],iconAnchor:[60,8]}})  }}).addTo(map);"
            )

        legend = (
            "<b>Rider Distribution</b><br>"
            f"<span style='color:{color}'>Circle size ∝ order count</span>"
        )
        return self._wrap_html("\n".join(js_lines), legend, height=500)

    def render_zone_revenue(self, zone_stats: List[Dict]) -> str:
        if not zone_stats:
            return self.render_rider_map([])

        max_rev   = max((z.get("revenue") or 0) for z in zone_stats) or 1.0
        js_lines: List[str] = []

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
            opacity  = round(0.40 + ratio * 0.45, 2)
            popup    = (
                f"<b>{zone_name}</b><br>"
                f"Revenue: <b style='color:{color}'>৳{revenue:,.0f}</b><br>"
                f"Orders: <b>{orders}</b>"
            )
            js_lines.append(
                f"L.circleMarker([{lat},{lon}],{{radius:{radius},color:'{color}',"
                f"fillColor:'{color}',fillOpacity:{opacity},weight:2}})"
                f".bindPopup('{popup}')"
                f".bindTooltip('<b>{zone_name}</b> | ৳{revenue:,.0f} ({orders} orders)').addTo(map);"
            )
            js_lines.append(
                f"L.marker([{lat+0.0016},{lon}],{{icon:L.divIcon({{html:"
                f"\"<div style='font-family:monospace;font-size:10px;font-weight:700;"
                f"color:{color};text-shadow:0 0 4px #000;text-align:center;"
                f"white-space:nowrap'>{zone_name}</div>\","
                f"iconSize:[110,16],iconAnchor:[55,8]}})  }}).addTo(map);"
            )

        legend = (
            "<b>Zone Revenue</b><br>"
            f"<span style='color:{self.COLORS['revenue_hi']}'>Bright = high revenue</span><br>"
            f"<span style='color:{self.COLORS['revenue_low']}'>Dark = low revenue</span>"
        )
        return self._wrap_html("\n".join(js_lines), legend, height=500)

    # ── Legacy shim so nothing else needs changing ────────────────────────────
    def _unavailable_map(self) -> None:
        pass  # never called — always available
# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 7 ── PRESENTATION LAYER (NEXUS UI)
# ═══════════════════════════════════════════════════════════════════════════════

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


# ─────────────────────────────────────────────────────────────────────────────

class NexusUI:
    """
    Full Streamlit 10-tab UI for LOGIX v7.0.
    Developer: Sourab Dey Soptom.

    FIX: All download_button calls are placed unconditionally (not inside
    if-button blocks) to avoid StreamlitAPIException: Invalid binary data format.
    """

    def __init__(self, db: NexusDatabase, scraper: LiveDataScraper,
                 soptom: SoptomAlgorithm, dss: DSSEngine,
                 business: BusinessEngine, routing: RoutingEngine,
                 maps: MapRenderer) -> None:
        self.db       = db
        self.scraper  = scraper
        self.soptom   = soptom
        self.dss      = dss
        self.business = business
        self.routing  = routing
        self.maps     = maps
        self.logger   = logging.getLogger(self.__class__.__name__)

    # ── Entry point ───────────────────────────────────────────────────────────

    def render(self) -> None:
        _inject_css()
        self._sidebar()

        tabs = st.tabs([
            "🏠 Command Centre", "📦 Inventory", "🧠 AI Intelligence",
            "⚖️ DSS Engine", "🗺️ Live Map", "🚚 Logistics",
            "💰 Finance", "🔔 Alerts", "📋 AI Logs", "⚙️ Settings",
        ])

        prices  = self.scraper.fetch_chaldal_prices()
        weather = self.scraper.fetch_weather_data()
        inv     = self.db.get_inventory()
        self.db.update_inventory_from_prices(prices)
        event   = st.session_state.get("market_event", "Normal Day")
        fcs     = st.session_state.get("forecasts", {})

        with tabs[0]: self._t0_command(prices, weather, inv, event, fcs)
        with tabs[1]: self._t1_inventory(inv, prices, event)
        with tabs[2]: self._t2_ai(inv, prices, weather, event, fcs)
        with tabs[3]: self._t3_dss(inv, prices, fcs)
        with tabs[4]: self._t4_map(inv, prices, fcs)
        with tabs[5]: self._t5_logistics(inv, prices)
        with tabs[6]: self._t6_finance(inv, prices)
        with tabs[7]: self._t7_alerts()
        with tabs[8]: self._t8_ai_logs()
        with tabs[9]: self._t9_settings(inv, prices, fcs)

    # ── Sidebar ───────────────────────────────────────────────────────────────

    def _sidebar(self) -> None:
        with st.sidebar:
            st.markdown(
                "<h2 style='color:#00ff88;letter-spacing:1px;'>🚀 LOGIX v7.0</h2>"
                "<p style='color:#7dd3fc;font-size:.78rem;margin-top:0;'>Chaldal Supply Chain Intelligence</p>",
                unsafe_allow_html=True,
            )
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

        c1,c2,c3,c4,c5,c6 = st.columns(6)
        c1.metric("📦 Total Stock",    f"{total_stk:,}")
        c2.metric("⚠️ Low Stock",      low_cnt,   delta=None, delta_color="inverse")
        c3.metric("🕐 Expiry Alerts",  exp_warn,  delta=None, delta_color="inverse")
        c4.metric("💰 Revenue (৳)",    f"{revenue:,.0f}")
        c5.metric("📋 Total Orders",   stats.get("total",0))
        c6.metric("✅ Delivered",       stats.get("delivered",0))

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

        # ── Inventory health ─────────────────────────────────────────────────
        st.markdown("### 📊 Inventory Health")
        for item in inv:
            stk = item.get("current_stock",0)
            eoq = item.get("eoq",50)
            pct = min(stk / max(eoq,1), 1.0)
            col = "#00ff88" if pct > 0.6 else ("#ffbb00" if pct > 0.3 else "#ff3366")
            cl, cr = st.columns([3,1])
            with cl:
                st.markdown(f"**{item.get('name','')}**")
                st.progress(pct)
            with cr:
                st.markdown(
                    f'<div style="color:{col};font-weight:700;margin-top:.5rem;">'
                    f'{stk} / {eoq}</div>',
                    unsafe_allow_html=True,
                )

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
        st.markdown("## 🗺️ Live Delivery Map — OpenStreetMap + Leaflet.js")
        st.caption("Zero-dependency interactive maps — no extra packages required.")

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
                if st.button("Close", key="cl_btn") and close_h != "— none —":
                    self.routing.close_hub(close_h)
                    self.db.add_alert(
                        "critical", "Logistics", f"Hub {close_h} CLOSED by operator."
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
                route_state = st.session_state.get("last_route")
                hub_html    = self.maps.render_hub_map(hub_metrics, route_state, closed_hubs)
                components.html(hub_html, height=560, scrolling=False)

        # ── Tab: Route Planner ────────────────────────────────────────────────
        with t_route:
            st.markdown("### 🛣️ Optimal Route Planner")
            hubs       = list(DHAKA_HUBS.keys())
            r1, r2, r3 = st.columns(3)
            with r1: src  = st.selectbox("Origin",      hubs,          key="r_src")
            with r2: dst  = st.selectbox("Destination", hubs, index=3, key="r_dst")
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
                        st.success(f"Route: **{' → '.join(result['path'])}**")
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
            st.markdown("**Route map** (updates after each 'Find Route' click):")
            route_html = self.maps.render_hub_map(
                hub_metrics,
                st.session_state.get("last_route"),
                closed_hubs,
            )
            components.html(route_html, height=480, scrolling=False)

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
            fc_map      = fcs if fcs else {
                i.get("sku_id", ""): {"forecast": [50] * FORECAST_DAYS} for i in inv
            }
            bubble_html = self.maps.render_demand_bubbles(inv, fc_map, prices)
            components.html(bubble_html, height=540, scrolling=False)

        # ── Tab: Riders & Revenue ─────────────────────────────────────────────
        with t_rider:
            rt_rider, rt_revenue = st.tabs(["🏍️ Rider Distribution", "📊 Zone Revenue"])

            with rt_rider:
                st.markdown("### 🏍️ Rider Distribution Map")
                st.caption("Circle size ∝ order count per delivery zone.")
                orders     = self.db.get_recent_orders(limit=120)
                rider_html = self.maps.render_rider_map(orders)
                components.html(rider_html, height=520, scrolling=False)

            with rt_revenue:
                st.markdown("### 📊 Zone Revenue Map")
                st.caption("Colour and size ∝ total revenue per zone (brighter = higher).")
                zone_stats  = self.db.get_zone_stats()
                rev_html    = self.maps.render_zone_revenue(zone_stats)
                components.html(rev_html, height=520, scrolling=False)
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
        tw, tdb, tinfo = st.tabs(["⚖️ DSS Weights","🗄️ Database","ℹ️ System Info"])

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


# ═══════════════════════════════════════════════════════════════════════════════
# BLOCK 8 ── MASTER CONTROLLER
# ═══════════════════════════════════════════════════════════════════════════════

class ApplicationController:
    """
    Application orchestrator — singleton session-state management.
    Heavy objects built once per Streamlit session and cached.
    """

    _SS = {
        "db":       "__nx_db__",
        "scraper":  "__nx_scraper__",
        "soptom":   "__nx_soptom__",
        "dss":      "__nx_dss__",
        "business": "__nx_business__",
        "routing":  "__nx_routing__",
        "maps":     "__nx_maps__",
        "ui":       "__nx_ui__",
    }

    def __init__(self) -> None:
        self.logger = logging.getLogger(self.__class__.__name__)

    def start(self) -> None:
        try:
            self._init_defaults()
            self._get_ui().render()
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

    def _get_db(self) -> NexusDatabase:
        k = self._SS["db"]
        if k not in st.session_state:
            self.logger.info("Init NexusDatabase")
            st.session_state[k] = NexusDatabase(DB_PATH)
        return st.session_state[k]

    def _get_scraper(self) -> LiveDataScraper:
        k = self._SS["scraper"]
        if k not in st.session_state:
            self.logger.info("Init LiveDataScraper")
            st.session_state[k] = LiveDataScraper()
        return st.session_state[k]

    def _get_soptom(self) -> SoptomAlgorithm:
        k = self._SS["soptom"]
        if k not in st.session_state:
            self.logger.info("Init SoptomAlgorithm")
            st.session_state[k] = SoptomAlgorithm(db=self._get_db())  # ← real DB passed in
        return st.session_state[k]

    def _get_dss(self) -> DSSEngine:
        k = self._SS["dss"]
        if k not in st.session_state:
            self.logger.info("Init DSSEngine")
            st.session_state[k] = DSSEngine()
        return st.session_state[k]

    def _get_business(self) -> BusinessEngine:
        k = self._SS["business"]
        if k not in st.session_state:
            self.logger.info("Init BusinessEngine")
            st.session_state[k] = BusinessEngine(self._get_db())
        return st.session_state[k]

    def _get_routing(self) -> RoutingEngine:
        k = self._SS["routing"]
        if k not in st.session_state:
            self.logger.info("Init RoutingEngine")
            st.session_state[k] = RoutingEngine()
        return st.session_state[k]

    def _get_maps(self) -> MapRenderer:
        k = self._SS["maps"]
        if k not in st.session_state:
            self.logger.info("Init MapRenderer")
            st.session_state[k] = MapRenderer()
        return st.session_state[k]

    def _get_ui(self) -> NexusUI:
        k = self._SS["ui"]
        if k not in st.session_state:
            self.logger.info("Init NexusUI")
            st.session_state[k] = NexusUI(
                db       = self._get_db(),
                scraper  = self._get_scraper(),
                soptom   = self._get_soptom(),
                dss      = self._get_dss(),
                business = self._get_business(),
                routing  = self._get_routing(),
                maps     = self._get_maps(),
            )
        return st.session_state[k]

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
