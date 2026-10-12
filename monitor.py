#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SEGNALATORE TRUMP & MERCATI  (notifiche Telegram)
=================================================

Ti avvisa su Telegram quando:
  1. Donald Trump scrive su Truth Social di Borsa/azioni, crypto, Fed/tassi/dollaro/materie prime
  2. La stampa riporta sue dichiarazioni a voce su questi temi
  3. Trump, Don Jr. o Eric depositano alla SEC acquisti/vendite (Form 4, 13D/13G, 144...)
  4. Le aziende collegate (Trump Media, American Bitcoin, ALT5 Sigma) depositano 8-K/10-Q/10-K
  5. Il wallet di tesoreria di World Liberty Financial muove fondi on-chain sopra soglia
  6. Escono notizie su acquisti/vendite delle entità Trump (incl. i report OGE 278-T di Trump)

Uso:
  python3 monitor.py              un controllo (è ciò che fa GitHub Actions ogni 5 minuti)
  python3 monitor.py --test       verifica tutte le fonti e manda un messaggio di prova
  python3 monitor.py --loop 60    controllo continuo ogni 60 secondi (uso sul PC)
  python3 monitor.py --dry-run    stampa i messaggi a schermo invece di inviarli

Variabili d'ambiente (su GitHub: Settings > Secrets and variables > Actions):
  TELEGRAM_BOT_TOKEN   token del bot creato con @BotFather          (obbligatorio)
  TELEGRAM_CHAT_ID     il tuo chat id (più id separati da virgola)   (obbligatorio)
  SEC_CONTACT          la tua email: la SEC chiede di identificarsi  (consigliato)

Nessuna libreria esterna: solo Python 3.9+ standard.
"""

import argparse
import email.utils
import gzip
import hashlib
import html
import json
import os
import re
import sys
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone

try:
    from zoneinfo import ZoneInfo
    TZ_LOCAL = ZoneInfo("Europe/Rome")
except Exception:  # pragma: no cover
    TZ_LOCAL = timezone.utc


# ════════════════════════════════════════════════════════════════════════════
#  CONFIGURAZIONE  –  puoi modificare liberamente questa sezione
# ════════════════════════════════════════════════════════════════════════════

# Argomenti dei post di Trump da segnalare: "borsa", "crypto", "macro"
ENABLED_TOPICS = ["borsa", "crypto", "macro"]

# Punteggio minimo perché un post venga segnalato (ogni parola chiave vale 1-3 punti).
#   2 = equilibrato (consigliato) · 3 = solo post più specifici · 1 = tutto
MIN_SCORE = 2

# Priorità minima da ricevere: "MEDIA" (tutto ciò che supera MIN_SCORE) oppure "ALTA"
MIN_PRIORITY = "MEDIA"

# Soglia in dollari per i movimenti on-chain del wallet World Liberty Financial
ONCHAIN_MIN_USD = 100_000

# Ogni quanti minuti controllare le notizie (Google News). Le altre fonti: ogni esecuzione.
NEWS_EVERY_MIN = 15

# Persone della famiglia Trump monitorate alla SEC (CIK = codice EDGAR)
SEC_PERSONS = [
    {"name": "Donald J. Trump", "cik": 947033},
    {"name": "Donald J. Trump Jr.", "cik": 2016181},
    {"name": "Eric Trump", "cik": 2057754},
]

# Aziende collegate alla famiglia: segnala i loro 8-K/10-Q/10-K (es. acquisti di bitcoin)
# e qualsiasi Form 4/13D/13G/144 in cui compare un membro della famiglia Trump.
# Se "cik" manca viene ricavato automaticamente dal ticker.
SEC_COMPANIES = [
    {"name": "Trump Media & Technology Group", "ticker": "DJT", "cik": 1849635},
    {"name": "American Bitcoin Corp", "ticker": "ABTC"},
    {"name": "ALT5 Sigma (tesoreria WLFI)", "ticker": "ALTS"},
]
SEC_COMPANY_FORMS = {"8-K", "8-K/A", "10-Q", "10-K", "10-K/A", "6-K", "13F-HR", "N-PORT-P"}
SEC_OWNERSHIP_FORMS_PREFIX = ("3", "4", "5", "144", "SC 13", "SCHEDULE 13")

# Wallet on-chain da sorvegliare (Ethereum, via Blockscout – nessuna chiave necessaria)
WALLETS = [
    {"name": "World Liberty Financial – Multisig tesoreria",
     "address": "0x5be9a4959308a0d0c7bc0870e319314d8d957dbb"},
]

# Fonti giornalistiche accettate per le notizie (None = tutte)
TRUSTED_SOURCES = [
    "Reuters", "Bloomberg", "CNBC", "Associated Press", "AP News", "The Wall Street Journal",
    "WSJ", "Financial Times", "Fox Business", "MarketWatch", "Axios", "Politico", "The Hill",
    "Yahoo Finance", "Barron's", "Business Insider", "CNN", "NBC News", "CBS News",
    "ABC News", "Forbes", "Fortune", "CoinDesk", "The Block", "Decrypt", "Cointelegraph",
    "Blockworks", "DL News", "Bitcoin Magazine", "Benzinga", "Investing.com", "Seeking Alpha",
    "The New York Times", "The Washington Post", "Newsweek", "Fox News", "Bloomberg.com",
    "Unchained", "CryptoSlate", "The Guardian", "BBC", "Al Jazeera", "Il Sole 24 ORE",
]

# Query Google News: dichiarazioni a voce di Trump sui mercati
STATEMENT_QUERIES = [
    'Trump (says OR said OR tells OR urges OR warns OR predicts OR touts OR remarks) '
    '(stocks OR "stock market" OR Dow OR Nasdaq OR "S&P 500" OR bitcoin OR crypto OR Fed OR '
    'Powell OR "interest rates" OR "rate cut" OR oil OR gold OR dollar OR markets) when:1d',
]

# Query Google News: movimenti di portafoglio delle entità Trump
#   (query, regex che il titolo deve contenere, etichetta)
_MOVE = (r"buy|bought|purchas|acquir|sell|sold|sale|stake|swap|moves?|moved|transfer|dump|"
         r"accumulat|treasury|disclos|holding|reserve|invest|trade|trades|position|deposit|withdr")
PORTFOLIO_QUERIES = [
    ('"World Liberty Financial" OR WLFI (buys OR bought OR sells OR sold OR acquires OR purchase '
     'OR swap OR treasury OR moves OR transfers OR wallet) when:1d',
     r"World Liberty|WLFI|USD1", "World Liberty Financial"),
    ('"Trump Media" (bitcoin OR BTC OR CRO OR treasury OR buys OR bought OR sells OR sold OR '
     'acquires OR stake OR ETF) when:1d',
     r"Trump Media|\bDJT\b|Truth\.Fi", "Trump Media (DJT)"),
    ('"American Bitcoin" (bitcoin OR BTC OR reserve OR buys OR acquires OR sells OR holdings) '
     'when:1d',
     r"American Bitcoin|\bABTC\b", "American Bitcoin (ABTC)"),
    ('("Eric Trump" OR "Donald Trump Jr" OR "Trump Jr." OR "Trump family" OR "Trump sons") '
     '(stake OR invests OR investment OR buys OR bought OR sells OR sold OR acquires OR shares) '
     'when:1d',
     r"Eric Trump|Trump Jr|Trump family|Trump sons|Trumps", "Famiglia Trump"),
    ('Trump ("periodic transaction report" OR "financial disclosure" OR "278-T" OR '
     '"disclosure shows" OR "trading disclosure") (stocks OR bonds OR trades OR purchases OR '
     'bought OR sold) when:2d',
     r"Trump", "Trump – operazioni personali (OGE)"),
    ('("$TRUMP" OR "TRUMP memecoin" OR "Trump meme coin" OR "Fight Fight Fight") (unlock OR '
     'sells OR buys OR treasury OR wallet OR moves) when:1d',
     r"\$?TRUMP|Trump meme|memecoin|Fight Fight Fight", "Memecoin $TRUMP"),
]

# Dopo quanti errori consecutivi di una fonte ricevi un avviso
FAIL_ALERT_THRESHOLD = 12

# ════════════════════════════════════════════════════════════════════════════
#  PAROLE CHIAVE  (regex, peso).  Peso 3 = molto specifico, 2 = chiaro, 1 = generico
#  Le regex senza (?-i) non distinguono maiuscole/minuscole.
# ════════════════════════════════════════════════════════════════════════════

COMPANIES = [
    "Apple", "Nvidia", "NVIDIA", "Intel", "Tesla", "Microsoft", "Amazon", "Google", "Alphabet",
    "Meta", "Boeing", "U.S. Steel", "US Steel", "Nippon Steel", "Exxon", "ExxonMobil", "Chevron",
    "Lockheed", "Raytheon", "General Motors", "Ford Motor", "Stellantis", "Pfizer", "Eli Lilly",
    "Johnson & Johnson", "JPMorgan", "Goldman Sachs", "Bank of America", "Citigroup",
    "Wells Fargo", "Walmart", "Oracle", "Palantir", "AMD", "Micron", "TSMC", "Samsung",
    "SoftBank", "OpenAI", "Netflix", "Warner Bros", "Coca-Cola", "Harley-Davidson",
    "Caterpillar", "John Deere", "BlackRock", "Berkshire", "Coinbase", "Trump Media", "Mattel",
    "Nike", "IBM", "Qualcomm", "Broadcom", "Cisco", "Hyundai", "Toyota", "Honda", "Volkswagen",
    "Novo Nordisk", "Merck", "AstraZeneca", "UnitedHealth", "Costco", "Home Depot", "Starbucks",
    "PayPal", "Robinhood", "Uber", "Anthropic", "xAI", "SpaceX", "Lithium Americas", "MP Materials",
]

TOPICS = {
    "borsa": {
        "label": "Azioni e Borsa", "emoji": "📈",
        "patterns": [
            (r"\bstock ?markets?\b", 2),
            (r"\bstocks?\b", 1),
            (r"\bwall street\b", 2),
            (r"\bdow( jones)?\b", 2),
            (r"\bnasdaq\b", 2),
            (r"\bs&p( ?500)?\b", 2),
            (r"\bmarkets? (is|are|was|were|will|went|hit|up|down|soar\w*|surg\w*|crash\w*|"
             r"record|boom\w*|rall\w*|tank\w*|plung\w*|jump\w*)\b", 2),
            (r"\b(record|all[- ]time) highs?\b", 1),
            (r"\bshares? (of|price|prices|buyback)\b", 2),
            (r"\b(ipo|earnings|dividends?|buybacks?)\b", 2),
            (r"\b(great|good|perfect|wonderful) time to (buy|invest)\b", 3),
            (r"\bbuy (now|stocks?|shares|the dip|american stocks)\b", 3),
            (r"(?-i:\bBUY\b)(?! AMERICAN)", 2),
            (r"\bsell[- ]?offs?\b|\bsell(ing)? (stocks?|shares)\b", 2),
            (r"\binvest(ing|ment|ments)? in\b", 1),
            (r"(?-i:\$[A-Z]{2,5}\b)", 3),
            (r"(?-i:\b(NYSE|NASDAQ|Nasdaq):\s?[A-Z]{1,5}\b)", 3),
            (r"\bmarket cap(italization)?\b", 2),
            (r"\b401\(?k\)?s?\b", 2),
            (r"\b(bull|bear) markets?\b", 2),
            (r"\b(stake|equity stake) in\b", 1),
            ("(?-i:\\b(" + "|".join(re.escape(c) for c in COMPANIES + [c.upper() for c in COMPANIES])
             + r")\b)", 2),
        ],
    },
    "crypto": {
        "label": "Crypto", "emoji": "🪙",
        "patterns": [
            (r"\bbitcoin\b", 2),
            (r"(?-i:\bBTC\b)", 2),
            (r"\bcrypto(currency|currencies)?\b", 2),
            (r"\bstablecoins?\b", 2),
            (r"\bethereum\b", 2),
            (r"(?-i:\bETH\b)", 2),
            (r"\bmeme ?coins?\b", 2),
            (r"\bworld liberty\b", 2),
            (r"(?-i:\b(WLFI|USD1|XRP)\b)", 2),
            (r"\bdigital assets?\b", 2),
            (r"\b(strategic )?bitcoin reserve\b|\bcrypto reserve\b", 3),
            (r"\bcrypto capital\b", 2),
            (r"\bblockchain\b", 1),
            (r"\b(coinbase|binance|solana|dogecoin)\b", 2),
            (r"(?-i:\b(GENIUS|CLARITY) Act\b)", 2),
        ],
    },
    "macro": {
        "label": "Fed, tassi, dollaro, materie prime", "emoji": "🏦",
        "patterns": [
            (r"\bfederal reserve\b", 2),
            (r"(?-i:\b(Fed|FED)\b)", 2),
            (r"\bpowell\b", 2),
            (r"(?-i:\b(Too Late|TOO LATE)\b)", 1),
            (r"\binterest rates?\b", 2),
            (r"\brates?\b", 1),
            (r"\brate cuts?\b|\bcut (interest )?rates\b|\blower (interest )?rates\b|"
             r"\brate hikes?\b|\bbasis points\b", 3),
            (r"\b(inflation|deflation|recession|stagflation)\b", 2),
            (r"(?-i:\b(CPI|PPI|GDP)\b)", 1),
            (r"\btreasur(y|ies) (yields?|bonds?|notes?|bills?)\b|\b(bond|10[- ]year) yields?\b", 2),
            (r"\byields?\b", 1),
            (r"\b10[- ]year\b", 2),
            (r"\bbonds?\b", 1),
            (r"\b(u\.?s\.?|us|american|strong|weak|the) dollar\b", 1),
            (r"\b(strong|weak|weaker|stronger) dollar\b|\breserve currency\b|"
             r"\bde-?dollari[sz]ation\b|\bdevalu\w*\b", 2),
            (r"\bcurrenc(y|ies)\b", 1),
            (r"\boil( prices?)?\b|\bcrude\b|(?-i:\bOPEC\b)", 2),
            (r"\bgasoline\b|\bgas prices?\b|\bnatural gas\b|(?-i:\bLNG\b)", 2),
            (r"\bgold\b(?! card)", 1),
            (r"\bsilver\b", 1),
            (r"\b(copper|lithium|uranium|nickel|cobalt|rare earths?|critical minerals)\b", 2),
            (r"\b(wheat|soybeans?|corn)\b", 1),
            (r"\bcommodit(y|ies)\b", 2),
            (r"\bdrill,? baby,? drill\b", 1),
        ],
    },
}

# Parole che rendono interessante un 8-K (estratto mostrato nella notifica)
EXCERPT_RX = re.compile(
    r"bitcoin|\bBTC\b|\bether\b|\bETH\b|crypto|digital asset|token|\bCRO\b|WLFI|USD1|treasury|"
    r"acquir|purchas|\bsold\b|sale of|divest|stake|investment|\bETF\b|holdings", re.I)

# ════════════════════════════════════════════════════════════════════════════
#  Da qui in poi il codice (non serve modificarlo)
# ════════════════════════════════════════════════════════════════════════════

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
STATE_PATH = os.path.join(BASE_DIR, "data", "state.json")

TRUMPSTRUTH_RSS = "https://trumpstruth.org/feed"
CNN_ARCHIVE_JSON = "https://ix.cnn.io/data/truth-social/truth_archive.json"
TRUTHSOCIAL_API = ("https://truthsocial.com/api/v1/accounts/107780257626128497/statuses"
                   "?exclude_replies=true&limit=40")
BLOCKSCOUT = "https://eth.blockscout.com/api/v2"

UA_BROWSER = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/126.0 Safari/537.36")

SEEN_LIMIT = 1500
MAX_POST_AGE_H = 24
MAX_FILING_AGE_D = 15

TX_CODES = {
    "P": ("🟢", "ACQUISTO sul mercato"),
    "S": ("🔴", "VENDITA sul mercato"),
    "A": ("🟢", "Assegnazione (grant/compenso)"),
    "D": ("🔴", "Cessione all'emittente"),
    "F": ("🔴", "Trattenuta per tasse"),
    "M": ("🔄", "Esercizio/conversione derivato"),
    "C": ("🔄", "Conversione"),
    "X": ("🔄", "Esercizio opzioni"),
    "G": ("🎁", "Donazione"),
    "L": ("🟢", "Piccolo acquisto"),
    "U": ("🔴", "Adesione a OPA"),
    "W": ("⚪", "Eredità/testamento"),
    "J": ("⚪", "Altra operazione"),
    "I": ("⚪", "Operazione discrezionale"),
    "K": ("⚪", "Swap/derivato"),
    "Z": ("⚪", "Trust di voto"),
    "E": ("⚪", "Scadenza derivato"),
    "H": ("⚪", "Scadenza derivato"),
    "O": ("🔄", "Esercizio opzioni out-of-the-money"),
}

ITEMS_8K = {
    "1.01": "accordo rilevante", "1.02": "fine accordo", "2.01": "acquisizione/cessione di attività",
    "2.02": "risultati finanziari", "2.03": "nuovo debito", "3.02": "emissione di azioni",
    "3.03": "modifica diritti azionisti", "5.02": "cambi nel management",
    "5.07": "voto assemblea", "7.01": "comunicazione al mercato", "8.01": "altri eventi",
    "9.01": "allegati",
}


# ─────────────────────────────── utilità ────────────────────────────────────

def log(*a):
    print(datetime.now(TZ_LOCAL).strftime("[%H:%M:%S]"), *a, flush=True)


def esc(s):
    return html.escape(s or "", quote=False)


def fmt_num(x, dec=0):
    try:
        x = float(x)
    except (TypeError, ValueError):
        return str(x)
    s = f"{x:,.{dec}f}"
    return s.replace(",", "X").replace(".", ",").replace("X", ".")


def fmt_usd(x):
    x = float(x)
    if abs(x) >= 1e9:
        return f"${fmt_num(x / 1e9, 2)} mld"
    if abs(x) >= 1e6:
        return f"${fmt_num(x / 1e6, 2)} mln"
    return f"${fmt_num(x, 0)}"


def fmt_time(dt):
    if not dt:
        return "?"
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(TZ_LOCAL).strftime("%d/%m/%Y %H:%M")


def now_utc():
    return datetime.now(timezone.utc)


def parse_iso(s):
    if not s:
        return None
    try:
        s = s.strip().replace("Z", "+00:00")
        dt = datetime.fromisoformat(s)
        return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def parse_rfc822(s):
    try:
        dt = email.utils.parsedate_to_datetime(s)
        return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    except Exception:
        return None


def html_to_text(s):
    if not s:
        return ""
    s = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", s)
    s = re.sub(r"(?i)<br\s*/?>|</p>|</div>|</blockquote>|</li>|</tr>|</h\d>", "\n", s)
    s = re.sub(r"<[^>]+>", " ", s)
    s = html.unescape(s).replace("\xa0", " ")
    s = re.sub(r"[ \t\r\f\v]+", " ", s)
    s = re.sub(r" *\n *", "\n", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def short_addr(a):
    return a[:6] + "…" + a[-4:] if a and len(a) > 12 else (a or "?")


def strip_ns(root):
    for el in root.iter():
        if isinstance(el.tag, str) and "}" in el.tag:
            el.tag = el.tag.split("}", 1)[1]
    return root


def first_text(root, *tags):
    """Primo testo non vuoto tra i tag indicati (ricerca in profondità)."""
    for tag in tags:
        for el in root.iter(tag):
            if el.text and el.text.strip():
                return el.text.strip()
    return None


def all_texts(root, tag):
    out = []
    for el in root.iter(tag):
        if el.text and el.text.strip() and el.text.strip() not in out:
            out.append(el.text.strip())
    return out


def news_key(title):
    t = re.sub(r"[^a-z0-9 ]", "", title.lower())
    t = re.sub(r"\s+", " ", t).strip()[:90]
    return hashlib.sha1(t.encode()).hexdigest()[:16]


# ─────────────────────────────── HTTP ───────────────────────────────────────

def http_get(url, headers=None, timeout=25, retries=2):
    h = {"User-Agent": UA_BROWSER, "Accept-Encoding": "gzip", "Accept": "*/*"}
    if headers:
        h.update(headers)
    last = None
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                data = r.read()
                if data[:2] == b"\x1f\x8b":
                    data = gzip.decompress(data)
                charset = r.headers.get_content_charset() or "utf-8"
                return data.decode(charset, errors="replace")
        except urllib.error.HTTPError as e:
            last = f"HTTP {e.code}"
            if e.code in (400, 401, 403, 404, 410):
                break
            if e.code == 429:
                time.sleep(6)
        except Exception as e:  # timeout, DNS, ecc.
            last = f"{type(e).__name__}: {e}"
        if attempt < retries:
            time.sleep(1.5 * (attempt + 1))
    raise RuntimeError(f"{last} su {url[:110]}")


def http_get_json(url, headers=None, timeout=25):
    return json.loads(http_get(url, headers=headers, timeout=timeout))


# ─────────────────────────────── Telegram ───────────────────────────────────

class Notifier:
    def __init__(self, token, chat_ids, dry_run=False):
        self.token = token
        self.chat_ids = [c.strip() for c in (chat_ids or "").split(",") if c.strip()]
        self.dry_run = dry_run or not token or not self.chat_ids
        self.sent = 0

    def send(self, text):
        if len(text) > 4090:
            text = text[:4000]
            text = re.sub(r"<[^>]*$", "", text)          # niente tag spezzati
            text = _close_tags(text) + "\n…"
        self.sent += 1
        if self.dry_run:
            print("\n" + "─" * 70 + "\n" + html.unescape(re.sub(r"</?(b|i|a[^>]*)>", "", text))
                  + "\n" + "─" * 70)
            return True
        ok_all = True
        for chat in self.chat_ids:
            ok_all &= self._send_one(chat, text)
            time.sleep(0.35)
        return ok_all

    def _send_one(self, chat, text, html_mode=True):
        url = f"https://api.telegram.org/bot{self.token}/sendMessage"
        payload = {"chat_id": chat, "text": text, "disable_web_page_preview": "true"}
        if html_mode:
            payload["parse_mode"] = "HTML"
        for _ in range(4):
            try:
                body = urllib.parse.urlencode(payload).encode()
                req = urllib.request.Request(url, data=body, headers={"User-Agent": "TrumpMonitor"})
                with urllib.request.urlopen(req, timeout=20) as r:
                    if json.loads(r.read().decode()).get("ok"):
                        return True
            except urllib.error.HTTPError as e:
                info = e.read().decode(errors="replace")
                if e.code == 429:
                    try:
                        wait = json.loads(info)["parameters"]["retry_after"]
                    except Exception:
                        wait = 5
                    time.sleep(min(int(wait) + 1, 60))
                    continue
                if e.code == 400 and html_mode and "parse" in info.lower():
                    plain = html.unescape(re.sub(r"<[^>]+>", "", text))
                    return self._send_one(chat, plain, html_mode=False)
                log(f"Telegram errore {e.code}: {info[:200]}")
                return False
            except Exception as e:
                log(f"Telegram errore: {e}")
                time.sleep(3)
        return False


def _close_tags(s):
    stack = []
    for m in re.finditer(r"<(/?)(b|i|a)\b[^>]*>", s):
        if m.group(1):
            if stack and stack[-1] == m.group(2):
                stack.pop()
        else:
            stack.append(m.group(2))
    return s + "".join(f"</{t}>" for t in reversed(stack))


# ─────────────────────────── motore parole chiave ───────────────────────────

_COMPILED = None


def _compiled():
    global _COMPILED
    if _COMPILED is None:
        _COMPILED = {}
        for key, t in TOPICS.items():
            _COMPILED[key] = [(re.compile(p, re.I), w) for p, w in t["patterns"]]
    return _COMPILED


def score_text(text):
    """Ritorna dict con punteggio/priorità/argomenti, oppure None se non rilevante."""
    if not text:
        return None
    hits, spans = [], []
    for key in ENABLED_TOPICS:
        for rx, w in _compiled().get(key, []):
            ms = list(rx.finditer(text))
            if ms:
                hits.append((key, ms[0].group(0).strip(), w))
                spans += [m.span() for m in ms]
    if not hits:
        return None
    topics = []
    for k, _, _ in hits:
        if k not in topics:
            topics.append(k)
    score = sum(w for _, _, w in hits) + (len(topics) - 1)
    strong = any(w >= 3 for _, _, w in hits)
    if score < MIN_SCORE and not strong:
        return None
    priority = "ALTA" if (strong or score >= 5) else "MEDIA"
    if MIN_PRIORITY == "ALTA" and priority != "ALTA":
        return None
    words = []
    for _, word, _ in sorted(hits, key=lambda h: (-h[2], -len(h[1]))):
        if not any(word.lower() in x.lower() for x in words):
            words.append(word)
    return {"score": score, "priority": priority, "topics": topics, "words": words[:8],
            "spans": spans}


def highlight(text, spans, maxlen=2500):
    cut = len(text) > maxlen
    text = text[:maxlen]
    merged = []
    for s, e in sorted((s, min(e, len(text))) for s, e in spans if s < len(text)):
        if merged and s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    out, pos = [], 0
    for s, e in merged:
        out.append(esc(text[pos:s]))
        out.append("<b>" + esc(text[s:e]) + "</b>")
        pos = e
    out.append(esc(text[pos:]))
    return "".join(out) + (" […]" if cut else "")


# ─────────────────────────────── stato ──────────────────────────────────────

def load_state():
    try:
        with open(STATE_PATH, encoding="utf-8") as f:
            st = json.load(f)
    except FileNotFoundError:
        st = {}
    except Exception as e:
        log(f"Stato illeggibile ({e}), riparto da zero")
        st = {}
    st.setdefault("seen", {})
    st.setdefault("init", {})
    st.setdefault("health", {})
    st.setdefault("cik_cache", {})
    return st


def save_state(st, original_dump=None):
    dump = json.dumps(st, ensure_ascii=False, indent=1, sort_keys=True)
    if original_dump is not None and dump == original_dump:
        return False
    os.makedirs(os.path.dirname(STATE_PATH), exist_ok=True)
    tmp = STATE_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(dump)
    os.replace(tmp, STATE_PATH)
    return True


def seen_set(st, name):
    return set(st["seen"].get(name, []))


def mark_seen(st, name, ids):
    lst = st["seen"].setdefault(name, [])
    known = set(lst)
    for i in ids:
        if i not in known:
            lst.append(i)
            known.add(i)
    if len(lst) > SEEN_LIMIT:
        del lst[: len(lst) - SEEN_LIMIT]


# ═══════════════════════ FONTE 1 – post di Trump ════════════════════════════

def _items_from_rss(xml_text):
    root = strip_ns(ET.fromstring(xml_text.encode("utf-8") if isinstance(xml_text, str) else xml_text))
    items = []
    for it in root.iter("item"):
        d = {}
        for ch in it:
            tag = ch.tag if isinstance(ch.tag, str) else ""
            if tag and tag not in d:
                d[tag] = (ch.text or "").strip()
                if ch.attrib:
                    d[tag + "@"] = dict(ch.attrib)
        items.append(d)
    return items


def parse_trumpstruth(xml_text):
    posts = []
    for d in _items_from_rss(xml_text):
        pid = d.get("originalId") or d.get("guid") or d.get("link")
        text = html_to_text(d.get("description", "")) or html.unescape(d.get("title", ""))
        text = re.sub(r"(?im)^\s*(view (image|video|media)|\[image\]|\[video\])\s*$", "", text).strip()
        posts.append({
            "id": str(pid),
            "created": parse_rfc822(d.get("pubDate", "")),
            "text": text,
            "url": d.get("originalUrl") or d.get("link"),
            "kind": (d.get("postType") or "original").lower(),
        })
    return posts


def parse_cnn(json_text, limit=150):
    data = json.loads(json_text)
    if isinstance(data, dict):
        data = data.get("posts") or data.get("data") or []
    posts = []
    for p in data[:limit]:
        content = html_to_text(p.get("content") or p.get("text") or "")
        posts.append({
            "id": str(p.get("id")),
            "created": parse_iso(p.get("created_at")),
            "text": content,
            "url": p.get("url") or f"https://truthsocial.com/@realDonaldTrump/{p.get('id')}",
            "kind": "repost" if content.startswith("RT ") else "original",
        })
    return posts


def parse_truthsocial(json_text):
    posts = []
    for p in json.loads(json_text):
        src = p.get("reblog") or p
        posts.append({
            "id": str(p.get("id")),
            "created": parse_iso(p.get("created_at")),
            "text": html_to_text(src.get("content", "")),
            "url": p.get("url") or src.get("url"),
            "kind": "repost" if p.get("reblog") else "original",
        })
    return posts


def fetch_truth_posts():
    errors = []
    for name, url, parser, timeout in (
        ("trumpstruth.org", TRUMPSTRUTH_RSS, parse_trumpstruth, 25),
        ("archivio CNN", CNN_ARCHIVE_JSON, parse_cnn, 90),
        ("Truth Social", TRUTHSOCIAL_API, parse_truthsocial, 25),
    ):
        try:
            posts = parser(http_get(url, timeout=timeout))
            posts = [p for p in posts if p["id"] and p["id"] != "None"]
            if posts:
                return posts, name
            errors.append(f"{name}: vuoto")
        except Exception as e:
            errors.append(f"{name}: {e}")
    raise RuntimeError(" | ".join(errors))


def format_post(p, sc, source_name, preview=False):
    pr_icon = "🔴" if sc["priority"] == "ALTA" else "🟡"
    topics = " · ".join(f'{TOPICS[t]["emoji"]} {TOPICS[t]["label"]}' for t in sc["topics"])
    kind = {"repost": " (repost)", "quote": " (citazione)", "reply": " (risposta)"}.get(p["kind"], "")
    head = "🧪 <b>ANTEPRIMA</b> (post già pubblicato)\n" if preview else ""
    return (
        f"{head}{pr_icon} <b>TRUMP su Truth Social{kind}</b> – priorità {sc['priority']}\n"
        f"{topics}\n"
        f"🔑 {esc(', '.join(sc['words']))}\n\n"
        f"{highlight(p['text'], sc['spans'])}\n\n"
        f"🕒 {fmt_time(p['created'])} (ora italiana)\n"
        f'🔗 <a href="{esc(p["url"])}">Apri il post</a> · fonte: {esc(source_name)}'
    )


def check_truth(st, notifier):
    posts, src = fetch_truth_posts()
    seen = seen_set(st, "truth")
    if not st["init"].get("truth"):
        mark_seen(st, "truth", [p["id"] for p in posts])
        st["init"]["truth"] = True
        return f"inizializzato ({len(posts)} post da {src})"
    cutoff = now_utc() - timedelta(hours=MAX_POST_AGE_H)
    new = [p for p in posts if p["id"] not in seen and (not p["created"] or p["created"] > cutoff)]
    new.sort(key=lambda p: p["created"] or now_utc())
    sent = 0
    for p in new:
        sc = score_text(p["text"])
        if sc:
            notifier.send(format_post(p, sc, src))
            sent += 1
        mark_seen(st, "truth", [p["id"]])
    mark_seen(st, "truth", [p["id"] for p in posts])
    return f"{len(new)} nuovi post, {sent} segnalati ({src})"


# ═══════════════════ FONTE 2/6 – notizie (Google News) ══════════════════════

def gnews_url(q):
    return "https://news.google.com/rss/search?" + urllib.parse.urlencode(
        {"q": q, "hl": "en-US", "gl": "US", "ceid": "US:en"})


def fetch_gnews(q):
    out = []
    for d in _items_from_rss(http_get(gnews_url(q))):
        title = html.unescape(d.get("title", "")).strip()
        source = html.unescape(d.get("source", "")).strip()
        if source and title.endswith(" - " + source):
            title = title[: -len(source) - 3].strip()
        out.append({"title": title, "source": source, "link": d.get("link", ""),
                    "date": parse_rfc822(d.get("pubDate", ""))})
    return out


def trusted(source):
    if not TRUSTED_SOURCES:
        return True
    s = source.lower()
    return any(t.lower() in s for t in TRUSTED_SOURCES)


def _news_line(n, extra=""):
    return (f'• <a href="{esc(n["link"])}">{esc(n["title"])}</a>\n'
            f'   <i>{esc(n["source"])} · {fmt_time(n["date"])}</i>{extra}')


def collect_news(st, preview=False):
    """Ritorna (dichiarazioni, portafoglio, tutte_le_chiavi)."""
    statements, portfolio, keys = [], {}, []
    seen = seen_set(st, "news")
    cutoff = now_utc() - timedelta(hours=48)
    errors = []
    for q in STATEMENT_QUERIES:
        try:
            items = fetch_gnews(q)
        except Exception as e:
            errors.append(str(e))
            continue
        for n in items:
            k = news_key(n["title"])
            keys.append(k)
            if (k in seen and not preview) or (n["date"] and n["date"] < cutoff):
                continue
            if "trump" not in n["title"].lower() or not trusted(n["source"]):
                continue
            sc = score_text(n["title"])
            if sc:
                n["sc"] = sc
                statements.append(n)
                seen.add(k)
    for q, must, label in PORTFOLIO_QUERIES:
        try:
            items = fetch_gnews(q)
        except Exception as e:
            errors.append(str(e))
            continue
        time.sleep(0.8)
        for n in items:
            k = news_key(n["title"])
            keys.append(k)
            if (k in seen and not preview) or (n["date"] and n["date"] < cutoff):
                continue
            if not re.search(must, n["title"], re.I) or not re.search(_MOVE, n["title"], re.I):
                continue
            if not trusted(n["source"]):
                continue
            portfolio.setdefault(label, []).append(n)
            seen.add(k)
    if errors and len(errors) == len(STATEMENT_QUERIES) + len(PORTFOLIO_QUERIES):
        raise RuntimeError("Google News non raggiungibile: " + errors[0])
    return statements, portfolio, keys


def format_statements(items, preview=False):
    items = sorted(items, key=lambda n: n["date"] or now_utc(), reverse=True)[:8]
    head = "🧪 <b>ANTEPRIMA</b>\n" if preview else ""
    lines = []
    for n in items:
        icon = "🔴" if n["sc"]["priority"] == "ALTA" else "🟡"
        lines.append(f"{icon} " + _news_line(n)[2:])
    return (f"{head}🗣️ <b>Dichiarazioni di Trump riportate dalla stampa</b>\n"
            f"<i>(parole a voce, interviste, conferenze)</i>\n\n" + "\n\n".join(lines))


def format_portfolio_news(groups, preview=False):
    head = "🧪 <b>ANTEPRIMA</b>\n" if preview else ""
    parts = []
    for label, items in groups.items():
        items = sorted(items, key=lambda n: n["date"] or now_utc(), reverse=True)[:5]
        parts.append(f"<b>{esc(label)}</b>\n" + "\n".join(_news_line(n) for n in items))
    return (f"{head}📰 <b>Notizie su acquisti/vendite delle entità Trump</b>\n\n"
            + "\n\n".join(parts))


def check_news(st, notifier):
    first = not st["init"].get("news")
    statements, portfolio, keys = collect_news(st)
    if first:
        mark_seen(st, "news", keys)
        st["init"]["news"] = True
        return f"inizializzato ({len(keys)} notizie)"
    if statements:
        notifier.send(format_statements(statements))
    if portfolio:
        notifier.send(format_portfolio_news(portfolio))
    mark_seen(st, "news", keys)
    return f"{len(statements)} dichiarazioni, {sum(len(v) for v in portfolio.values())} notizie portafoglio"


# ═══════════════════════ FONTE 3/4 – SEC EDGAR ══════════════════════════════

def sec_headers():
    contact = os.environ.get("SEC_CONTACT", "").strip() or "trump-monitor@users.noreply.github.com"
    return {"User-Agent": f"TrumpMarketMonitor/1.0 personal research ({contact})",
            "Accept-Encoding": "gzip"}


def sec_get(url, timeout=30):
    time.sleep(0.2)  # max ~5 richieste/s (limite SEC: 10/s)
    return http_get(url, headers=sec_headers(), timeout=timeout)


def resolve_ciks(st):
    entities = [dict(p, kind="person") for p in SEC_PERSONS]
    missing = []
    need_map = any(not c.get("cik") and c["ticker"] not in st["cik_cache"] for c in SEC_COMPANIES)
    tmap = {}
    if need_map:
        try:
            for v in json.loads(sec_get("https://www.sec.gov/files/company_tickers.json")).values():
                tmap[v["ticker"].upper()] = int(v["cik_str"])
        except Exception as e:
            log(f"Mappa ticker SEC non disponibile: {e}")
    for c in SEC_COMPANIES:
        cik = c.get("cik") or st["cik_cache"].get(c["ticker"]) or tmap.get(c["ticker"].upper())
        if cik:
            st["cik_cache"][c["ticker"]] = cik
            entities.append(dict(c, cik=cik, kind="company"))
        else:
            missing.append(c["ticker"])
    return entities, missing


def sec_recent(cik, limit=40):
    data = json.loads(sec_get(f"https://data.sec.gov/submissions/CIK{int(cik):010d}.json"))
    r = data.get("filings", {}).get("recent", {})
    out = []
    for i in range(min(limit, len(r.get("accessionNumber", [])))):
        def g(k):
            v = r.get(k, [])
            return v[i] if i < len(v) else ""
        out.append({"acc": g("accessionNumber"), "form": g("form"), "date": g("filingDate"),
                    "accepted": g("acceptanceDateTime"), "doc": g("primaryDocument"),
                    "desc": g("primaryDocDescription"), "items": g("items"), "cik": int(cik)})
    return data.get("name", ""), out


def filing_base(f):
    return f"https://www.sec.gov/Archives/edgar/data/{f['cik']}/{f['acc'].replace('-', '')}"


def filing_index_url(f):
    return f"{filing_base(f)}/{f['acc']}-index.htm"


def raw_doc_url(f):
    return f"{filing_base(f)}/{re.sub(r'^xsl[^/]+/', '', f['doc'])}"


def is_ownership_form(form):
    return form.upper().startswith(SEC_OWNERSHIP_FORMS_PREFIX)


def parse_ownership_xml(xml_text):
    """Form 3/4/5: emittente, proprietari, transazioni e posizioni."""
    root = strip_ns(ET.fromstring(xml_text.encode("utf-8")))

    def t(el, path):
        x = el.find(path)
        return x.text.strip() if x is not None and x.text and x.text.strip() else None

    res = {"issuer": t(root, "issuer/issuerName"), "ticker": t(root, "issuer/issuerTradingSymbol"),
           "owners": [t(o, "reportingOwnerId/rptOwnerName") for o in root.findall("reportingOwner")],
           "txs": [], "holdings": []}
    for path, deriv in (("nonDerivativeTable/nonDerivativeTransaction", False),
                        ("derivativeTable/derivativeTransaction", True)):
        for tx in root.findall(path):
            res["txs"].append({
                "security": t(tx, "securityTitle/value"), "date": t(tx, "transactionDate/value"),
                "code": t(tx, "transactionCoding/transactionCode"),
                "shares": t(tx, "transactionAmounts/transactionShares/value"),
                "price": t(tx, "transactionAmounts/transactionPricePerShare/value"),
                "ad": t(tx, "transactionAmounts/transactionAcquiredDisposedCode/value"),
                "after": t(tx, "postTransactionAmounts/sharesOwnedFollowingTransaction/value"),
                "di": t(tx, "ownershipNature/directOrIndirectOwnership/value"),
                "nature": t(tx, "ownershipNature/natureOfOwnership/value"), "deriv": deriv})
    for path in ("nonDerivativeTable/nonDerivativeHolding", "derivativeTable/derivativeHolding"):
        for h in root.findall(path):
            res["holdings"].append({
                "security": t(h, "securityTitle/value"),
                "after": t(h, "postTransactionAmounts/sharesOwnedFollowingTransaction/value"),
                "di": t(h, "ownershipNature/directOrIndirectOwnership/value"),
                "nature": t(h, "ownershipNature/natureOfOwnership/value")})
    return res


def parse_generic_xml(xml_text):
    """13D / 13G / 144: estrazione per nome dei tag (formati XML EDGAR)."""
    root = strip_ns(ET.fromstring(xml_text.encode("utf-8")))
    return {
        "issuer": first_text(root, "issuerName", "nameOfIssuer"),
        "cls": first_text(root, "securitiesClassTitle", "titleOfClass"),
        "event": first_text(root, "dateOfEvent", "eventDateRequiresFilingThisStatement"),
        "persons": all_texts(root, "reportingPersonName") or all_texts(root, "nameOfPersonForWhoseAccountTheSecuritiesAreToBeSold"),
        "amount": first_text(root, "aggregateAmountOwned",
                             "reportingPersonBeneficiallyOwnedAggregateNumberOfShares"),
        "pct": first_text(root, "percentOfClass", "classPercent"),
        "tx_desc": first_text(root, "transactionDesc"),
        "funds": first_text(root, "fundsSource"),
        "units_sold": first_text(root, "noOfUnitsSold"),
        "market_value": first_text(root, "aggregateMarketValue"),
        "sale_date": first_text(root, "approxSaleDate"),
    }


def _tx_line(tx):
    icon, label = TX_CODES.get((tx["code"] or "").upper(), ("⚪", f"Codice {tx['code']}"))
    if tx["code"] in (None, "") and tx["ad"]:
        icon, label = ("🟢", "Acquisizione") if tx["ad"] == "A" else ("🔴", "Cessione")
    line = f"{icon} <b>{label}</b>"
    if tx["shares"]:
        line += f" · {fmt_num(tx['shares'])} {'derivati' if tx['deriv'] else 'azioni'}"
    try:
        px = float(tx["price"] or 0)
        if px > 0:
            line += f" @ ${fmt_num(px, 2)}"
            if tx["shares"]:
                line += f" (≈ {fmt_usd(px * float(tx['shares']))})"
    except ValueError:
        pass
    sub = []
    if tx["date"]:
        sub.append(f"data {tx['date']}")
    if tx["security"]:
        sub.append(esc(tx["security"][:60]))
    if tx["after"]:
        sub.append(f"dopo: {fmt_num(tx['after'])}")
    if tx["di"] == "I":
        sub.append("indiretta" + (f" ({esc(tx['nature'][:50])})" if tx["nature"] else ""))
    return line + ("\n     <i>" + " · ".join(sub) + "</i>" if sub else "")


def excerpt_8k(f):
    """Cerca nel comunicato (ex-99) o nel documento principale le frasi su acquisti/vendite."""
    docs = []
    try:
        idx = json.loads(sec_get(f"{filing_base(f)}/index.json"))
        names = [i["name"] for i in idx.get("directory", {}).get("item", [])]
        docs += [n for n in names if re.search(r"ex-?99", n, re.I) and n.lower().endswith((".htm", ".html", ".txt"))][:2]
    except Exception:
        pass
    docs.append(f["doc"])
    found = []
    for d in docs:
        try:
            text = html_to_text(sec_get(f"{filing_base(f)}/{d}"))
        except Exception:
            continue
        for sent in re.split(r"(?<=[.!?])\s+", text):
            sent = sent.strip()
            if 40 < len(sent) < 450 and EXCERPT_RX.search(sent) and sent not in found:
                found.append(sent)
            if len(found) >= 3:
                break
        if found:
            break
    out = " ".join(found)
    return out[:700] + ("…" if len(out) > 700 else "")


def format_filing(f, entity, preview=False):
    """Costruisce il messaggio per un deposito SEC. Ritorna None se non va segnalato."""
    form = f["form"].upper()
    head = "🧪 <b>ANTEPRIMA</b> (deposito già pubblicato)\n" if preview else ""
    link = f'🔗 <a href="{filing_index_url(f)}">Documento SEC</a>'
    who = esc(entity["name"])

    if form in ("3", "4", "5", "3/A", "4/A", "5/A"):
        o = parse_ownership_xml(sec_get(raw_doc_url(f)))
        owners = ", ".join(x for x in o["owners"] if x) or entity["name"]
        if entity["kind"] == "company" and "trump" not in owners.lower():
            return None
        issuer = esc(o["issuer"] or "?") + (f" ({esc(o['ticker'])})" if o["ticker"] else "")
        lines = [_tx_line(tx) for tx in o["txs"][:12]]
        if not lines and o["holdings"]:
            lines = [f"📌 Posizione: {fmt_num(h['after'])} – {esc((h['security'] or '')[:60])}"
                     + (" (indiretta)" if h["di"] == "I" else "") for h in o["holdings"][:8]]
        kind = {"3": "posizione iniziale", "4": "variazione partecipazione", "5": "riepilogo annuale"}
        buys = any((tx["code"] or "") in "PL" and tx["code"] for tx in o["txs"])
        sells = any((tx["code"] or "") in "SDFU" and tx["code"] for tx in o["txs"])
        tag = "🟢🔴 ACQUISTI E VENDITE" if buys and sells else ("🟢 ACQUISTO" if buys else ("🔴 VENDITA" if sells else ""))
        return (f"{head}🏛️ <b>SEC Form {form}</b> – {kind.get(form[0], '')} {('· ' + tag) if tag else ''}\n"
                f"👤 <b>{esc(owners)}</b>\n🏢 Società: <b>{issuer}</b>\n\n"
                + ("\n".join(lines) or "(nessuna transazione elencata)")
                + f"\n\n📅 Depositato: {f['date']}\n{link}")

    if form.startswith(("SC 13", "SCHEDULE 13", "144")):
        g = {}
        if f["doc"].lower().endswith(".xml"):
            try:
                g = parse_generic_xml(sec_get(raw_doc_url(f)))
            except Exception as e:
                log(f"XML {form} non leggibile: {e}")
        persons = ", ".join(g.get("persons") or []) or entity["name"]
        if entity["kind"] == "company" and "trump" not in persons.lower():
            return None
        if form.startswith("144"):
            body = (f"🔴 <b>Intenzione di VENDERE</b> (Form 144)\n"
                    f"🏢 Società: <b>{esc(g.get('issuer') or '?')}</b>\n"
                    + (f"Quantità: {fmt_num(g['units_sold'])} titoli\n" if g.get("units_sold") else "")
                    + (f"Valore: {fmt_usd(g['market_value'])}\n" if g.get("market_value") else "")
                    + (f"Data vendita prevista: {esc(g['sale_date'])}\n" if g.get("sale_date") else ""))
        else:
            kind = "13D (partecipazione attiva >5%)" if "13D" in form else "13G (partecipazione passiva >5%)"
            amend = " – aggiornamento" if form.endswith("/A") else ""
            body = (f"📊 <b>Schedule {kind}{amend}</b>\n"
                    f"🏢 Società: <b>{esc(g.get('issuer') or '?')}</b>\n"
                    + (f"Possesso: {fmt_num(g['amount'])} titoli" if g.get("amount") else "")
                    + (f" = <b>{esc(g['pct'])}%</b>" if g.get("pct") else "") + "\n"
                    + (f"Data evento: {esc(g['event'])}\n" if g.get("event") else ""))
            detail = g.get("funds") or ""
            if g.get("tx_desc") and "not effected any" not in g["tx_desc"]:
                detail = g["tx_desc"] + " " + detail
            if detail.strip():
                body += f"📝 <i>{esc(detail.strip()[:600])}</i>\n"
        return (f"{head}🏛️ <b>SEC – {esc(form)}</b>\n👤 <b>{esc(persons)}</b>\n{body}\n"
                f"📅 Depositato: {f['date']}\n{link}")

    if entity["kind"] == "company" and form in SEC_COMPANY_FORMS:
        items = ""
        if f.get("items"):
            items = ", ".join(f"{i} {ITEMS_8K.get(i, '')}".strip() for i in f["items"].split(","))
        ex = ""
        if form.startswith(("8-K", "6-K")):
            try:
                ex = excerpt_8k(f)
            except Exception:
                ex = ""
        kind = {"8-K": "evento rilevante", "8-K/A": "evento rilevante (rettifica)",
                "10-Q": "trimestrale", "10-K": "annuale", "10-K/A": "annuale (rettifica)",
                "13F-HR": "portafoglio trimestrale 13F", "6-K": "comunicazione", "N-PORT-P": "portafoglio fondo"}
        return (f"{head}🏢 <b>{who}</b> – SEC {esc(form)} ({kind.get(form, '')})\n"
                + (f"📋 {esc(items)}\n" if items else "")
                + (f"📝 <i>{esc(f['desc'])}</i>\n" if f.get("desc") and f["desc"] != form else "")
                + (f"\n💬 «{esc(ex)}»\n" if ex else "")
                + f"\n📅 Depositato: {f['date']}\n{link}")

    if entity["kind"] == "person":
        return (f"{head}🏛️ <b>SEC – {esc(form)}</b>\n👤 <b>{who}</b>\n"
                + (f"📝 {esc(f['desc'])}\n" if f.get("desc") else "")
                + f"📅 Depositato: {f['date']}\n{link}")
    return None


def check_sec(st, notifier):
    entities, missing = resolve_ciks(st)
    first = not st["init"].get("sec")
    seen = seen_set(st, "sec")
    cutoff = (now_utc() - timedelta(days=MAX_FILING_AGE_D)).strftime("%Y-%m-%d")
    new_total, sent, errors = 0, 0, []
    for ent in entities:
        try:
            _, filings = sec_recent(ent["cik"])
        except Exception as e:
            errors.append(f"{ent['name']}: {e}")
            continue
        for f in reversed(filings):  # dal più vecchio al più recente
            if f["acc"] in seen:
                continue
            seen.add(f["acc"])
            mark_seen(st, "sec", [f["acc"]])
            if first or f["date"] < cutoff:
                continue
            form = f["form"].upper()
            if ent["kind"] == "company" and form not in SEC_COMPANY_FORMS and not is_ownership_form(form):
                continue
            new_total += 1
            try:
                msg = format_filing(f, ent)
            except Exception as e:
                log(f"Errore lettura {f['acc']}: {e}")
                msg = (f"🏛️ <b>SEC – {esc(f['form'])}</b> · {esc(ent['name'])}\n"
                       f"📅 {f['date']}\n🔗 <a href=\"{filing_index_url(f)}\">Documento SEC</a>")
            if msg:
                notifier.send(msg)
                sent += 1
    if errors and len(errors) == len(entities):
        raise RuntimeError("SEC non raggiungibile: " + errors[0])
    if first:
        st["init"]["sec"] = True
        return f"inizializzato ({len(entities)} entità" + (f", ticker non trovati: {missing}" if missing else "") + ")"
    note = f"; errori: {len(errors)}" if errors else ""
    return f"{new_total} nuovi depositi, {sent} segnalati{note}"


# ═══════════════════ FONTE 5 – wallet on-chain (Blockscout) ═════════════════

def _token_amount(total, token):
    try:
        dec = int((total or {}).get("decimals") or token.get("decimals") or 18)
        return int((total or {}).get("value") or 0) / (10 ** dec)
    except (TypeError, ValueError):
        return 0.0


def cp_label(cp):
    """Nome leggibile della controparte (es. 'Coinbase', 'Uniswap'), se Blockscout lo conosce."""
    if not cp:
        return None
    for tag in ((cp.get("metadata") or {}).get("tags") or []):
        if isinstance(tag, dict) and tag.get("name"):
            return tag["name"]
    for tag in (cp.get("public_tags") or []):
        if isinstance(tag, dict) and (tag.get("display_name") or tag.get("label")):
            return tag.get("display_name") or tag.get("label")
    name = cp.get("name")
    if name and name not in ("GnosisSafeProxy", "TransparentUpgradeableProxy", "ERC1967Proxy"):
        return name
    return None


def wallet_movements(address):
    """Raggruppa per transazione i trasferimenti valutati in USD."""
    addr = address.lower()
    txs = {}
    data = http_get_json(f"{BLOCKSCOUT}/addresses/{address}/token-transfers?type=ERC-20")
    for it in data.get("items", []):
        token = it.get("token") or {}
        if (token.get("reputation") or "").lower() == "scam":
            continue
        rate = token.get("exchange_rate")
        if not rate:
            continue  # token senza prezzo = quasi sempre spam/airdrop
        amount = _token_amount(it.get("total"), token)
        usd = amount * float(rate)
        frm = ((it.get("from") or {}).get("hash") or "").lower()
        to = ((it.get("to") or {}).get("hash") or "").lower()
        direction = "in" if to == addr else ("out" if frm == addr else None)
        if not direction:
            continue
        cp = it.get("from") if direction == "in" else it.get("to")
        tx = txs.setdefault(it["transaction_hash"], {"hash": it["transaction_hash"],
                                                     "time": parse_iso(it.get("timestamp")), "legs": []})
        tx["legs"].append({"dir": direction, "symbol": token.get("symbol") or "?", "amount": amount,
                           "usd": usd, "cp": (cp or {}).get("hash"), "cp_name": cp_label(cp)})
    # ETH nativo (transazioni normali + interne)
    try:
        price = float(http_get_json(f"{BLOCKSCOUT}/stats").get("coin_price") or 0)
    except Exception:
        price = 0
    if price:
        for kind in ("transactions", "internal-transactions"):
            try:
                d = http_get_json(f"{BLOCKSCOUT}/addresses/{address}/{kind}")
            except Exception:
                continue
            for it in d.get("items", []):
                val = int(it.get("value") or 0) / 1e18
                if val <= 0:
                    continue
                h = it.get("hash") or it.get("transaction_hash")
                frm = ((it.get("from") or {}).get("hash") or "").lower()
                to = ((it.get("to") or {}).get("hash") or "").lower()
                direction = "in" if to == addr else ("out" if frm == addr else None)
                if not direction or not h:
                    continue
                cp = it.get("from") if direction == "in" else it.get("to")
                tx = txs.setdefault(h, {"hash": h, "time": parse_iso(it.get("timestamp")), "legs": []})
                tx["legs"].append({"dir": direction, "symbol": "ETH", "amount": val, "usd": val * price,
                                   "cp": (cp or {}).get("hash"), "cp_name": cp_label(cp)})
    return sorted(txs.values(), key=lambda t: t["time"] or now_utc())


def format_wallet_tx(w, tx, preview=False):
    ins = [l for l in tx["legs"] if l["dir"] == "in"]
    outs = [l for l in tx["legs"] if l["dir"] == "out"]
    if ins and outs:
        kind = "🔄 <b>SWAP</b> – venduto " + ", ".join(sorted({l["symbol"] for l in outs})) + \
               " → comprato " + ", ".join(sorted({l["symbol"] for l in ins}))
    elif ins:
        kind = "🟢 <b>ENTRATA</b> di fondi (acquisto/ricezione)"
    else:
        kind = "🔴 <b>USCITA</b> di fondi (vendita/trasferimento)"
    lines = []
    for l in sorted(tx["legs"], key=lambda l: -l["usd"])[:8]:
        sign = "+" if l["dir"] == "in" else "−"
        cp = esc(l["cp_name"]) if l.get("cp_name") else short_addr(l["cp"])
        arrow = "da" if l["dir"] == "in" else "verso"
        lines.append(f"{sign}{fmt_num(l['amount'], 2 if l['amount'] < 1000 else 0)} {esc(l['symbol'])} "
                     f"(≈ {fmt_usd(l['usd'])}) {arrow} {cp}")
    head = "🧪 <b>ANTEPRIMA</b> (movimento già avvenuto)\n" if preview else ""
    return (f"{head}🐋 <b>{esc(w['name'])}</b>\n{kind}\n\n" + "\n".join(lines) +
            f"\n\n🕒 {fmt_time(tx['time'])}\n"
            f'🔗 <a href="https://etherscan.io/tx/{tx["hash"]}">Vedi su Etherscan</a>')


def check_wallets(st, notifier, preview=False):
    msgs, report = [], []
    for w in WALLETS:
        key = "wallet:" + w["address"].lower()
        txs = wallet_movements(w["address"])
        seen = seen_set(st, key)
        first = not st["init"].get(key)
        cutoff = now_utc() - timedelta(days=3)
        n = 0
        for tx in txs:
            if tx["hash"] in seen and not preview:
                continue
            big = max((l["usd"] for l in tx["legs"]), default=0) >= ONCHAIN_MIN_USD
            recent = not tx["time"] or tx["time"] > cutoff
            if big and (preview or (not first and recent)):
                msgs.append(format_wallet_tx(w, tx, preview))
                n += 1
        if not preview:
            mark_seen(st, key, [t["hash"] for t in txs])
            st["init"][key] = True
        report.append(f"{w['name'].split(' – ')[0]}: {n} movimenti segnalati")
    if preview:
        return msgs
    for m in msgs:
        notifier.send(m)
    return ", ".join(report)


# ═══════════════════════════ orchestrazione ═════════════════════════════════

SOURCE_LABELS = {
    "truth": "Post di Trump (Truth Social)",
    "news": "Notizie e dichiarazioni (Google News)",
    "sec": "Depositi SEC (famiglia e aziende)",
    "wallets": "Wallet on-chain WLFI",
}


def run_source(name, fn, st, notifier):
    h = st["health"].setdefault(name, {"fails": 0})
    try:
        result = fn(st, notifier)
        if h.get("alerted"):
            notifier.send(f"✅ Fonte di nuovo raggiungibile: <b>{SOURCE_LABELS[name]}</b>")
        st["health"][name] = {"fails": 0}
        log(f"{SOURCE_LABELS[name]}: {result}")
        return True, result
    except Exception as e:
        h["fails"] = h.get("fails", 0) + 1
        h["last_error"] = str(e)[:300]
        log(f"ERRORE {SOURCE_LABELS[name]}: {e}")
        if os.environ.get("MONITOR_DEBUG"):
            traceback.print_exc()
        if h["fails"] >= FAIL_ALERT_THRESHOLD and not h.get("alerted"):
            notifier.send(f"⚠️ <b>{SOURCE_LABELS[name]}</b> non risponde da {h['fails']} controlli "
                          f"consecutivi.\n<i>{esc(str(e)[:300])}</i>\nTi avviso quando torna attiva.")
            h["alerted"] = True
        return False, str(e)


def news_due():
    return (now_utc().minute % NEWS_EVERY_MIN) < 5


def run_once(st, notifier, news=None):
    """news=None → decide l'orologio (ogni NEWS_EVERY_MIN minuti); True/False → forzato."""
    first_ever = not st.get("started_at")
    results = {}
    results["truth"] = run_source("truth", check_truth, st, notifier)
    results["sec"] = run_source("sec", check_sec, st, notifier)
    results["wallets"] = run_source("wallets", check_wallets, st, notifier)
    if first_ever or (news_due() if news is None else news):
        results["news"] = run_source("news", check_news, st, notifier)
    if first_ever:
        st["started_at"] = now_utc().isoformat(timespec="seconds")
        lines = [f"{'✅' if ok else '❌'} {SOURCE_LABELS[k]}" + ("" if ok else f" – <i>{esc(r[:120])}</i>")
                 for k, (ok, r) in results.items()]
        notifier.send(
            "🚀 <b>Segnalatore Trump & Mercati attivo</b>\n\n" + "\n".join(lines) +
            f"\n\nArgomenti: {', '.join(TOPICS[t]['label'] for t in ENABLED_TOPICS)}\n"
            f"Soglia on-chain: {fmt_usd(ONCHAIN_MIN_USD)}\n"
            "Da ora riceverai solo le novità (i contenuti già pubblicati sono stati ignorati).")
    return results


def run_test(st, notifier):
    """Verifica le fonti e manda anteprime con contenuti reali già pubblicati (non salva lo stato)."""
    lines, previews = [], []
    tok = "✅" if notifier.token else "❌ manca TELEGRAM_BOT_TOKEN"
    chat = "✅" if notifier.chat_ids else "❌ manca TELEGRAM_CHAT_ID"
    sec_c = "✅" if os.environ.get("SEC_CONTACT") else "⚠️ SEC_CONTACT non impostato (consigliato)"
    lines.append(f"Bot Telegram: {tok} · Chat: {chat}\nContatto SEC: {sec_c}")

    try:
        posts, src = fetch_truth_posts()
        matched = [(p, score_text(p["text"])) for p in posts]
        matched = [(p, s) for p, s in matched if s]
        lines.append(f"✅ Post di Trump: {len(posts)} letti da {src}, {len(matched)} sui tuoi argomenti")
        if matched:
            p, s = matched[0]
            previews.append(format_post(p, s, src, preview=True))
    except Exception as e:
        lines.append(f"❌ Post di Trump: {esc(str(e)[:200])}")

    try:
        entities, missing = resolve_ciks(st)
        latest = None
        for ent in entities:
            name, filings = sec_recent(ent["cik"], limit=10)
            for f in filings:
                if ent["kind"] == "person" or f["form"].upper() in SEC_COMPANY_FORMS:
                    if not latest or f["date"] > latest[0]["date"]:
                        latest = (f, ent)
                    break
        lines.append(f"✅ SEC: {len(entities)} entità monitorate"
                     + (f" (ticker non trovati: {', '.join(missing)})" if missing else ""))
        if latest:
            msg = format_filing(latest[0], latest[1], preview=True)
            if msg:
                previews.append(msg)
    except Exception as e:
        lines.append(f"❌ SEC: {esc(str(e)[:200])}")

    try:
        wmsgs = check_wallets(st, notifier, preview=True)
        lines.append(f"✅ Wallet WLFI: raggiungibile, {len(wmsgs)} movimenti sopra "
                     f"{fmt_usd(ONCHAIN_MIN_USD)} tra gli ultimi trasferimenti")
        if wmsgs:
            previews.append(wmsgs[-1])
    except Exception as e:
        lines.append(f"❌ Wallet WLFI: {esc(str(e)[:200])}")

    try:
        statements, portfolio, keys = collect_news(st, preview=True)
        lines.append(f"✅ Google News: {len(keys)} notizie lette, {len(statements)} dichiarazioni, "
                     f"{sum(len(v) for v in portfolio.values())} su portafogli (ultime 48 h)")
        if statements:
            previews.append(format_statements(statements[:3], preview=True))
        if portfolio:
            previews.append(format_portfolio_news({k: v[:2] for k, v in portfolio.items()}, preview=True))
    except Exception as e:
        lines.append(f"❌ Google News: {esc(str(e)[:200])}")

    notifier.send("🧪 <b>Test del segnalatore</b>\n\n" + "\n".join(lines) +
                  ("\n\nQui sotto alcune anteprime con contenuti già pubblicati." if previews else ""))
    for m in previews:
        notifier.send(m)
    print("\n".join(re.sub(r"<[^>]+>", "", l) for l in lines))


def load_env_file():
    path = os.path.join(BASE_DIR, ".env")
    if not os.path.exists(path):
        return
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                k, v = line.split("=", 1)
                os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))


def main():
    ap = argparse.ArgumentParser(description="Segnalatore Trump & Mercati")
    ap.add_argument("--test", action="store_true", help="verifica fonti e invia anteprime")
    ap.add_argument("--loop", type=int, metavar="SECONDI", help="controllo continuo (uso su PC)")
    ap.add_argument("--dry-run", action="store_true", help="stampa i messaggi invece di inviarli")
    ap.add_argument("--reset", action="store_true", help="cancella lo stato e riparte da zero")
    args = ap.parse_args()

    load_env_file()
    notifier = Notifier(os.environ.get("TELEGRAM_BOT_TOKEN", "").strip(),
                        os.environ.get("TELEGRAM_CHAT_ID", ""), dry_run=args.dry_run)
    if notifier.dry_run and not args.dry_run:
        log("ATTENZIONE: token o chat id Telegram mancanti → i messaggi vengono solo stampati")

    if args.reset and os.path.exists(STATE_PATH):
        os.remove(STATE_PATH)
        log("Stato cancellato")

    st = load_state()
    original = json.dumps(st, ensure_ascii=False, indent=1, sort_keys=True)

    if args.test:
        run_test(st, notifier)
        return

    if args.loop:
        log(f"Controllo continuo ogni {args.loop} s – Ctrl+C per fermare")
        last_news = 0.0
        while True:
            try:
                do_news = time.time() - last_news >= NEWS_EVERY_MIN * 60
                if do_news:
                    last_news = time.time()
                run_once(st, notifier, news=do_news)
                save_state(st)
            except KeyboardInterrupt:
                raise
            except Exception as e:
                log(f"Errore inatteso: {e}")
            time.sleep(max(20, args.loop))
    else:
        run_once(st, notifier)
        changed = save_state(st, original)
        log(f"Fatto. Messaggi inviati: {notifier.sent}. Stato {'aggiornato' if changed else 'invariato'}.")


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nFermato.")
