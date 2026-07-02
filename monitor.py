#!/usr/bin/env python3
"""
John Pye auction monitor.

Watches John Pye searches for your keywords (or full refined search URLs) and
emails you only the NEW lots. No login required - the search results are plain
server-rendered HTML, and every lot carries a stable numeric ID in its URL
(/Event/LotDetails/<ID>/...) which is used to tell new lots from ones already seen.

Each line of keywords.txt is one "watch". It can be:
  * a plain keyword            -> unifi
  * a labelled keyword         -> UniFi kit | unifi
  * a full search URL          -> https://www.johnpyeauctions.co.uk/Browse?FullTextQuery=dewalt&StatusFilter=active_only
  * a labelled full URL        -> 110V @ Brum | https://www.johnpyeauctions.co.uk/Browse/R200440056/BIRMINGHAM?FullTextQuery=110v&CategoryID=9&SortFilterOptions=1&StatusFilter=active_only

Paste a URL straight from your browser's address bar to reuse any refine
(region, category, sort, price range) exactly as you set it on the site.

Test locally:  python monitor.py --dry-run
"""

import os
import re
import sys
import json
import time
import html as htmllib
import smtplib
import argparse
import datetime as dt
from urllib.parse import quote, urlparse, urlunparse, parse_qsl, urlencode
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

from bs4 import BeautifulSoup

# Prefer curl_cffi, which can impersonate a real Chrome browser's TLS/HTTP
# fingerprint - this is what gets past Cloudflare's 403 on data-centre IPs.
try:
    from curl_cffi import requests as http
    _CAN_IMPERSONATE = True
except ImportError:                      # falls back to plain requests locally
    import requests as http
    _CAN_IMPERSONATE = False

# --- Config -----------------------------------------------------------------

BASE = "https://www.johnpyeauctions.co.uk"
# Default template used when a keywords.txt line is a plain keyword (not a URL).
DEFAULT_TEMPLATE = BASE + "/Browse?FullTextQuery={kw}&StatusFilter=active_only"

HERE = os.path.dirname(os.path.abspath(__file__))
SEEN_FILE = os.path.join(HERE, "seen.json")
KEYWORDS_FILE = os.path.join(HERE, "keywords.txt")

USER_AGENT = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")
# curl_cffi impersonation targets, tried in order until one is accepted.
IMPERSONATE = ["chrome124", "chrome120", "chrome110", "safari17_0"]
BROWSER_HEADERS = {
    "User-Agent": USER_AGENT,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,"
              "image/avif,image/webp,image/apng,*/*;q=0.8",
    "Accept-Language": "en-GB,en;q=0.9",
    "Referer": BASE + "/",
    "Upgrade-Insecure-Requests": "1",
}
REQUEST_TIMEOUT = 30
DELAY_BETWEEN_REQUESTS = 3     # seconds, be polite
MAX_PAGES = 10                 # safety cap for very broad searches
PRUNE_AFTER_DAYS = 120

LOT_RE = re.compile(r"/Event/LotDetails/(\d+)/")
LOT_HREF_RE = re.compile(r'href="([^"]*?/Event/LotDetails/(\d+)/[^"]*)"')
PRICE_RE = re.compile(r"£\s?([\d,]+(?:\.\d{2})?)")
PAGE_RE = re.compile(r"[?&]page=(\d+)")
NO_RESULTS = "there were no results"
BLOCK_MARKERS = ("Just a moment", "cf-browser-verification", "Attention Required",
                 "Checking your browser")


# --- Watches (keyword / URL parsing) ---------------------------------------

def load_watches():
    if not os.path.exists(KEYWORDS_FILE):
        return []
    watches = []
    with open(KEYWORDS_FILE, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            label, _, rest = line.partition("|")
            if rest.strip():                       # "label | keyword-or-url"
                label, target = label.strip(), rest.strip()
            else:
                label, target = None, line
            if target.lower().startswith("http"):
                url = target
                label = label or _label_from_url(url)
            else:
                url = DEFAULT_TEMPLATE.format(kw=quote(target))
                label = label or target
            watches.append((label, url))
    return watches


def _label_from_url(url):
    q = dict(parse_qsl(urlparse(url).query))
    if q.get("FullTextQuery"):
        return q["FullTextQuery"]
    parts = [p for p in urlparse(url).path.split("/") if p]
    return parts[-1] if parts else url


def _with_page(url, page):
    parts = urlparse(url)
    q = [(k, v) for (k, v) in parse_qsl(parts.query) if k.lower() != "page"]
    if page:
        q.append(("page", str(page)))
    return urlunparse(parts._replace(query=urlencode(q)))


# --- Scraping ---------------------------------------------------------------

def fetch(url):
    """Fetch a URL as a real browser. Retries across TLS fingerprints on 403."""
    last = None
    attempts = IMPERSONATE if _CAN_IMPERSONATE else [None]
    for imp in attempts:
        try:
            if _CAN_IMPERSONATE:
                r = http.get(url, headers=BROWSER_HEADERS, impersonate=imp,
                             timeout=REQUEST_TIMEOUT)
            else:
                r = http.get(url, headers=BROWSER_HEADERS, timeout=REQUEST_TIMEOUT)
            if r.status_code in (403, 429, 503):   # blocked - try next fingerprint
                last = f"{r.status_code} on {imp or 'plain'}"
                time.sleep(2)
                continue
            r.raise_for_status()
            return r.text
        except Exception as e:
            last = e
            time.sleep(2)
    raise RuntimeError(f"blocked/failed after {len(attempts)} attempt(s): {last}")


def page_status(html_text):
    """Classify a page so we never treat an anomaly as a real empty result."""
    if any(m in html_text for m in BLOCK_MARKERS):
        return "blocked"
    if LOT_RE.search(html_text):
        return "ok"
    if NO_RESULTS in html_text.lower():
        return "empty"
    return "anomalous"


def parse_lots(html_text):
    """Return {lot_id: {title, url, price}} for every lot on one results page."""
    soup = BeautifulSoup(html_text, "html.parser")

    # Title = the richest anchor text for each lot id (heading anchor wins over
    # the image/empty anchors that point at the same lot).
    titles, urls = {}, {}
    for a in soup.find_all("a", href=True):
        m = LOT_RE.search(a["href"])
        if not m:
            continue
        lot_id = m.group(1)
        text = " ".join(a.get_text(" ", strip=True).split())
        if lot_id not in titles or len(text) > len(titles[lot_id]):
            titles[lot_id] = text
            url = a["href"]
            urls[lot_id] = BASE + url if url.startswith("/") else url

    # Price = last £ value inside each lot's slice of the raw HTML. Taking the
    # LAST one skips any "ORIGINAL RRP £x" that sits inside the title and lands
    # on the current bid, which is rendered after the title.
    order, first_pos = [], {}
    for m in LOT_HREF_RE.finditer(html_text):
        lid = m.group(2)
        if lid not in first_pos:
            first_pos[lid] = m.start()
            order.append(lid)

    lots = {}
    for i, lid in enumerate(order):
        start = first_pos[lid]
        end = first_pos[order[i + 1]] if i + 1 < len(order) else len(html_text)
        found = PRICE_RE.findall(htmllib.unescape(html_text[start:end]))
        price = "£" + found[-1] if found else None
        title = titles.get(lid, "")
        if not title:
            title = urls.get(lid, "").rstrip("/").split("/")[-1].replace("-", " ").title()
        lots[lid] = {"title": title, "url": urls.get(lid, ""), "price": price}
    return lots


def scrape(url):
    """Fetch a watch URL, following pagination. Returns (status, lots)."""
    all_lots, seen_pages, page = {}, set(), 0
    status = "empty"
    while page < MAX_PAGES:
        page_url = _with_page(url, page)
        html_text = fetch(page_url)
        st = page_status(html_text)
        if st in ("blocked", "anomalous"):
            return st, all_lots
        if st == "ok":
            status = "ok"
        lots = parse_lots(html_text)
        new_ids = set(lots) - set(all_lots)
        all_lots.update(lots)
        # find the next page number, if any
        nums = {int(n) for n in PAGE_RE.findall(html_text)}
        nxt = min((n for n in nums if n > page and n not in seen_pages), default=None)
        seen_pages.add(page)
        if not new_ids or nxt is None:
            break
        page = nxt
        time.sleep(DELAY_BETWEEN_REQUESTS)
    return status, all_lots


# --- State ------------------------------------------------------------------

def load_seen():
    if not os.path.exists(SEEN_FILE):
        return {}
    try:
        with open(SEEN_FILE, encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError):
        return {}


def save_seen(seen):
    cutoff = dt.datetime.utcnow() - dt.timedelta(days=PRUNE_AFTER_DAYS)
    kept = {}
    for lid, rec in seen.items():
        try:
            first = dt.datetime.fromisoformat(rec.get("first_seen", ""))
        except ValueError:
            first = dt.datetime.utcnow()
        if first >= cutoff:
            kept[lid] = rec
    with open(SEEN_FILE, "w", encoding="utf-8") as f:
        json.dump(kept, f, indent=2, ensure_ascii=False)


# --- Email ------------------------------------------------------------------

def build_email(new_lots, baseline=False):
    now = dt.datetime.now().strftime("%a %d %b %Y, %H:%M")
    n = len(new_lots)
    subject = (f"John Pye monitor started - tracking {n} current lots" if baseline
               else f"John Pye: {n} new lot(s) matching your watches")

    by_label = {}
    for label, info in new_lots:
        by_label.setdefault(label, []).append(info)

    intro = ("Monitoring is now live. These are the lots currently matching your "
             "watches - you won't be told about them again. From now on you'll only "
             "hear about brand-new listings." if baseline
             else "New lots have appeared since the last check:")
    text = [intro, ""]
    html = [f"<p style='font:15px/1.5 Arial,sans-serif'>{htmllib.escape(intro)}</p>"]

    for label in sorted(by_label):
        items = by_label[label]
        text.append(f"=== {label} ({len(items)}) ===")
        html.append(f"<h3 style='font:16px Arial,sans-serif;margin:18px 0 6px'>"
                    f"{htmllib.escape(label)} <span style='color:#888;font-weight:normal'>"
                    f"({len(items)})</span></h3><ul style='margin:0;padding-left:18px'>")
        for info in items:
            price = f" — {info['price']}" if info.get("price") else ""
            text.append(f"  {info['title']}{price}\n    {info['url']}")
            html.append("<li style='font:14px/1.5 Arial,sans-serif;margin-bottom:8px'>"
                        f"<a href='{htmllib.escape(info['url'])}'>{htmllib.escape(info['title'])}</a>"
                        f"{htmllib.escape(price)}</li>")
        html.append("</ul>")
        text.append("")

    text.append(f"Checked {now}.")
    html.append(f"<p style='font:12px Arial,sans-serif;color:#999;margin-top:20px'>Checked {now}.</p>")
    return subject, "\n".join(text), "".join(html)


def send_email(subject, text_body, html_body):
    host, port = os.environ["SMTP_HOST"], int(os.environ.get("SMTP_PORT", "587"))
    user, passwd = os.environ["SMTP_USER"], os.environ["SMTP_PASS"]
    to_addr = os.environ["EMAIL_TO"]
    from_addr = os.environ.get("EMAIL_FROM", user)

    msg = MIMEMultipart("alternative")
    msg["Subject"], msg["From"], msg["To"] = subject, from_addr, to_addr
    msg.attach(MIMEText(text_body, "plain", "utf-8"))
    msg.attach(MIMEText("<div>" + html_body + "</div>", "html", "utf-8"))
    with smtplib.SMTP(host, port, timeout=REQUEST_TIMEOUT) as s:
        s.starttls()
        s.login(user, passwd)
        s.sendmail(from_addr, [a.strip() for a in to_addr.split(",")], msg.as_string())


# --- Main -------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true",
                    help="parse and print, but never email or save state")
    args = ap.parse_args()

    watches = load_watches()
    if not watches:
        print("No watches in keywords.txt - nothing to do.")
        return

    seen = load_seen()
    baseline = len(seen) == 0
    now_iso = dt.datetime.utcnow().isoformat(timespec="seconds")
    new_lots = []

    for label, url in watches:
        try:
            status, lots = scrape(url)
        except Exception as e:
            print(f"[warn] '{label}' failed: {e}", file=sys.stderr)
            continue
        if status in ("blocked", "anomalous"):
            print(f"[warn] '{label}': page looked {status} (possible block) - skipped, "
                  f"not treated as empty", file=sys.stderr)
            continue
        fresh = 0
        for lid, info in lots.items():
            if lid in seen:
                continue
            seen[lid] = {"title": info["title"], "url": info["url"],
                         "first_seen": now_iso, "label": label}
            new_lots.append((label, info))
            fresh += 1
        print(f"'{label}': {len(lots)} on page, {fresh} new")
        time.sleep(DELAY_BETWEEN_REQUESTS)

    if args.dry_run:
        print(f"\n[dry-run] {len(new_lots)} new; state NOT saved, no email sent.")
        for label, info in new_lots:
            print(f"  [{label}] {info['title']} {info.get('price') or ''} -> {info['url']}")
        return

    if new_lots:
        subject, text_body, html_body = build_email(new_lots, baseline=baseline)
        try:
            send_email(subject, text_body, html_body)
            print(f"Emailed {len(new_lots)} new lot(s).")
        except Exception as e:
            print(f"[error] email failed: {e}", file=sys.stderr)
            sys.exit(1)   # don't save state, so we retry next run
    else:
        print("No new lots.")
    save_seen(seen)


if __name__ == "__main__":
    main()
