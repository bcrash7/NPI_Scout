#!/usr/bin/env python3
"""
concierge_npi_scout.py
Look up a physician by NPI and open a self-contained HTML report in Chrome.
Usage: python main.py 1234567890 [--json] [--no-google] [--no-scrape]
"""

from __future__ import annotations

import argparse
import base64
import datetime as dt
import json
import os
import re
import sys
import tempfile
import time
import urllib.parse
import webbrowser
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Optional

import requests

try:
    from bs4 import BeautifulSoup
    _HAVE_BS4 = True
except ImportError:
    _HAVE_BS4 = False


# ----------------------------------------------------------------------------
# Configuration
# ----------------------------------------------------------------------------
GOOGLE_API_KEY = os.environ.get("GOOGLE_MAPS_API_KEY", "").strip()
CENSUS_API_KEY = os.environ.get("CENSUS_API_KEY", "").strip()
ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "").strip()
# Model that reads the provider's website and extracts practice type / services /
# insurances / certifications. Swap if your API account needs a different string
# (e.g. "claude-opus-4-8" or "claude-haiku-4-5-20251001").
LLM_MODEL = "claude-sonnet-4-6"
print(f"[config] Google key: {'detected' if GOOGLE_API_KEY else 'MISSING'}; "
      f"Census key: {'detected' if CENSUS_API_KEY else 'MISSING'}; "
      f"Anthropic key: {'detected' if ANTHROPIC_API_KEY else 'MISSING'}", file=sys.stderr)

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36 ConciergeNPIScout/1.3"
)

NPPES_URL = "https://npiregistry.cms.hhs.gov/api/"
CMS_DATA_JSON = "https://data.cms.gov/data.json"
CMS_DATA_API = "https://data.cms.gov/data-api/v1/dataset/{uuid}/data"
CENSUS_BASE = "https://api.census.gov/data/{year}/acs/acs5"
CENSUS_GEOCODER = "https://geocoding.geo.census.gov/geocoder/locations/onelineaddress"
CENSUS_YEARS_TO_TRY = [2023, 2022, 2021]

OSM_STATICMAP = "https://staticmap.openstreetmap.de/staticmap.php"

_STATE_FIPS = {
    "AL": "01", "AK": "02", "AZ": "04", "AR": "05", "CA": "06", "CO": "08",
    "CT": "09", "DE": "10", "DC": "11", "FL": "12", "GA": "13", "HI": "15",
    "ID": "16", "IL": "17", "IN": "18", "IA": "19", "KS": "20", "KY": "21",
    "LA": "22", "ME": "23", "MD": "24", "MA": "25", "MI": "26", "MN": "27",
    "MS": "28", "MO": "29", "MT": "30", "NE": "31", "NV": "32", "NH": "33",
    "NJ": "34", "NM": "35", "NY": "36", "NC": "37", "ND": "38", "OH": "39",
    "OK": "40", "OR": "41", "PA": "42", "RI": "44", "SC": "45", "SD": "46",
    "TN": "47", "TX": "48", "UT": "49", "VT": "50", "VA": "51", "WA": "53",
    "WV": "54", "WI": "55", "WY": "56", "PR": "72",
}

INSURANCE_KEYWORDS = [
    "medicare", "medicaid", "aetna", "cigna", "humana", "united healthcare",
    "unitedhealthcare", "blue cross", "blue shield", "bcbs", "anthem", "tricare",
    "kaiser", "oscar", "molina", "wellcare", "centene", "self-pay", "self pay",
    "out of network", "out-of-network", "ppo", "hmo", "epo", "we accept most",
]
SERVICE_KEYWORDS = [
    # Primary care / concierge internal medicine
    "annual physical", "wellness exam", "preventive care", "preventative care",
    "chronic disease", "chronic care", "diabetes", "hypertension", "cardiology",
    "telemedicine", "telehealth", "same-day", "same day", "urgent care",
    "lab work", "bloodwork", "blood work", "vaccinations", "immunizations",
    "weight management", "weight loss", "hormone", "iv therapy", "concierge",
    "membership", "house call", "house calls", "geriatric", "pediatric",
    "women's health", "men's health", "physical therapy", "dermatology",
    "screening", "ekg", "ecg", "spirometry", "ultrasound",
    # Aesthetic / med-spa (so a med spa is recognizable, not mislabeled as primary care)
    "med spa", "medspa", "medical spa", "aesthetic", "aesthetics", "esthetician",
    "botox", "dysport", "jeuveau", "neurotoxin", "botulinum", "dermal filler",
    "filler", "lip filler", "injectable", "injectables", "microneedling",
    "chemical peel", "facial", "facials", "hydrafacial", "dermaplaning",
    "laser hair removal", "laser", "ipl", "photofacial", "coolsculpting",
    "body contouring", "skin tightening", "morpheus8", "prp",
    "platelet-rich plasma", "microblading", "skin rejuvenation", "anti-aging",
    "anti aging", "wrinkle", "peels", "hormone replacement", "testosterone",
    "trt", "semaglutide", "tirzepatide", "vitamin injection", "b12 injection",
]

_CERT_PATTERNS = [
    r"board[\s-]*certified(?:\s+in\s+[A-Za-z ,&/]+)?",
    r"diplomate[\s,]+(?:of\s+)?the\s+american\s+board\s+of\s+[A-Za-z ,&/]+",
    r"american\s+board\s+of\s+[A-Za-z ,&/]+",
    r"fellow\s+of\s+the\s+american\s+(?:college|academy)\s+of\s+[A-Za-z ,&/]+",
]
_RECOGNITION_PATTERNS = [
    r"castle\s+connolly", r"top\s+doctor[s]?", r"best\s+doctor[s]?",
    r"patients?'?\s+choice\s+award", r"america'?s?\s+top\s+\w+",
]


# ----------------------------------------------------------------------------
# HTTP helpers
# ----------------------------------------------------------------------------
_SESSION = requests.Session()
_SESSION.headers.update({"User-Agent": USER_AGENT})


def _get(url, *, params=None, headers=None, timeout=25, retries=3, expect="json"):
    last_err = None
    for attempt in range(retries):
        try:
            r = _SESSION.get(url, params=params, headers=headers, timeout=timeout)
            if r.status_code == 429:
                time.sleep(2 * (attempt + 1))
                continue
            r.raise_for_status()
            if expect == "json":
                return r.json()
            if expect == "text":
                return r.text
            if expect == "bytes":
                return r.content
            return r
        except Exception as e:  # noqa: BLE001
            last_err = e
            time.sleep(1.0 * (attempt + 1))
    if last_err:
        print(f"    [warn] GET failed ({url.split('?')[0]}): {last_err}", file=sys.stderr)
    return None


def _post(url, *, json_body, headers=None, timeout=25, retries=2):
    last_err = None
    last_body = None
    for attempt in range(retries):
        try:
            r = _SESSION.post(url, json=json_body, headers=headers, timeout=timeout)
            if r.status_code >= 400:
                last_body = r.text
            r.raise_for_status()
            return r.json()
        except Exception as e:  # noqa: BLE001
            last_err = e
            time.sleep(1.0 * (attempt + 1))
    if last_err:
        print(f"    [warn] POST failed ({url.split('?')[0]}): {last_err}", file=sys.stderr)
        if last_body:
            print(f"    [warn] response body: {last_body[:600]}", file=sys.stderr)
    return None


def fetch_image_b64(url, *, headers=None, max_bytes=5_000_000) -> Optional[str]:
    r = _get(url, headers=headers, expect="resp", timeout=25, retries=2)
    if r is None:
        return None
    ctype = (r.headers.get("Content-Type", "") or "").split(";")[0].strip().lower()
    if not ctype.startswith("image/"):
        return None
    data = r.content
    if not data or len(data) > max_bytes:
        return None
    return f"data:{ctype};base64,{base64.b64encode(data).decode('ascii')}"


# ----------------------------------------------------------------------------
# Data model
# ----------------------------------------------------------------------------
@dataclass
class Address:
    purpose: str = ""
    line1: str = ""
    line2: str = ""
    city: str = ""
    state: str = ""
    postal: str = ""
    phone: str = ""
    lat: Optional[float] = None
    lng: Optional[float] = None
    area_median_household_income: Optional[int] = None
    area_per_capita_income: Optional[int] = None
    area_median_home_value: Optional[int] = None
    census_year: Optional[int] = None
    photo_data_uris: list[str] = field(default_factory=list)
    street_view_data_uri: str = ""
    satellite_data_uri: str = ""
    map_data_uri: str = ""
    map_link: str = ""

    @property
    def zip5(self) -> str:
        m = re.match(r"\d{5}", self.postal or "")
        return m.group(0) if m else ""

    @property
    def is_office(self) -> bool:
        return self.purpose in ("LOCATION", "PRACTICE LOCATION")

    def one_line(self) -> str:
        bits = [self.line1, self.line2, f"{self.city}, {self.state} {self.postal}".strip()]
        return ", ".join(b for b in bits if b and b.strip(", "))


@dataclass
class ReviewSource:
    source: str = ""
    rating: Optional[float] = None
    review_count: Optional[int] = None
    url: str = ""
    note: str = ""


@dataclass
class ProviderProfile:
    npi: str = ""
    retrieved_at: str = ""
    first_name: str = ""
    last_name: str = ""
    middle_name: str = ""
    credential: str = ""
    gender: str = ""
    sole_proprietor: str = ""
    organization_name: str = ""
    enumeration_type: str = ""
    enumeration_date: str = ""
    last_updated: str = ""
    years_in_practice_proxy: Optional[float] = None
    specializations: list[str] = field(default_factory=list)
    primary_taxonomy: str = ""
    licenses: list[str] = field(default_factory=list)
    addresses: list[Address] = field(default_factory=list)
    medicare_beneficiaries: Optional[int] = None
    medicare_total_services: Optional[float] = None
    medicare_total_payment: Optional[float] = None
    medicare_drug_beneficiaries: Optional[int] = None
    medicare_medical_beneficiaries: Optional[int] = None
    medicare_data_year: Optional[int] = None
    medicare_provider_type: str = ""
    website: str = ""
    practice_type: str = ""
    practice_summary: str = ""
    website_services: list[str] = field(default_factory=list)
    website_insurances: list[str] = field(default_factory=list)
    reviews: list[ReviewSource] = field(default_factory=list)
    board_certifications: list[str] = field(default_factory=list)
    recognitions: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    sources_used: list[str] = field(default_factory=list)

    @property
    def full_name(self) -> str:
        return " ".join(b for b in [self.first_name, self.last_name] if b) or self.organization_name


# ----------------------------------------------------------------------------
# NPPES
# ----------------------------------------------------------------------------
def fetch_nppes(npi: str, prof: ProviderProfile) -> None:
    data = _get(NPPES_URL, params={"version": "2.1", "number": npi})
    if not data or not data.get("results"):
        prof.notes.append("NPPES: no record found for this NPI.")
        return
    prof.sources_used.append("NPPES NPI Registry")
    rec = data["results"][0]
    prof.enumeration_type = rec.get("enumeration_type", "")
    basic = rec.get("basic", {})
    prof.first_name = basic.get("first_name", "")
    prof.last_name = basic.get("last_name", "")
    prof.middle_name = basic.get("middle_name", "")
    prof.credential = basic.get("credential", "")
    prof.gender = basic.get("gender", "")
    prof.sole_proprietor = basic.get("sole_proprietor", "")
    prof.organization_name = basic.get("organization_name", "") or basic.get("name", "")
    prof.enumeration_date = basic.get("enumeration_date", "")
    prof.last_updated = basic.get("last_updated", "")

    if prof.enumeration_date:
        try:
            ed = dt.datetime.strptime(prof.enumeration_date, "%Y-%m-%d").date()
            prof.years_in_practice_proxy = round((dt.date.today() - ed).days / 365.25, 1)
        except ValueError:
            pass

    for tax in rec.get("taxonomies", []):
        desc = tax.get("desc", "")
        if desc:
            prof.specializations.append(desc + (" (primary)" if tax.get("primary") else ""))
            if tax.get("primary"):
                prof.primary_taxonomy = desc
        lic, st = tax.get("license", ""), tax.get("state", "")
        if lic:
            prof.licenses.append(f"{lic} ({st})" if st else lic)
    if not prof.primary_taxonomy and prof.specializations:
        prof.primary_taxonomy = prof.specializations[0].replace(" (primary)", "")

    for ad in rec.get("addresses", []):
        prof.addresses.append(Address(
            purpose=ad.get("address_purpose", ""), line1=ad.get("address_1", ""),
            line2=ad.get("address_2", ""), city=ad.get("city", ""),
            state=ad.get("state", ""), postal=ad.get("postal_code", ""),
            phone=ad.get("telephone_number", ""),
        ))
    for ad in rec.get("practiceLocations", []) or []:
        prof.addresses.append(Address(
            purpose="PRACTICE LOCATION", line1=ad.get("address_1", ""),
            line2=ad.get("address_2", ""), city=ad.get("city", ""),
            state=ad.get("state", ""), postal=ad.get("postal_code", ""),
            phone=ad.get("telephone_number", ""),
        ))


# ----------------------------------------------------------------------------
# CMS Medicare (by Provider)
# ----------------------------------------------------------------------------
_CMS_UUID_CACHE: dict[str, Any] = {}


def discover_cms_dataset_uuid(override: str = ""):
    if override:
        return override, None
    if "uuid" in _CMS_UUID_CACHE:
        return _CMS_UUID_CACHE["uuid"], _CMS_UUID_CACHE.get("year")
    catalog = _get(CMS_DATA_JSON, timeout=40)
    best = None
    if catalog and isinstance(catalog.get("dataset"), list):
        for ds in catalog["dataset"]:
            title = ds.get("title") or ""
            t = title.lower()
            if ("by provider" not in t or "physician" not in t
                    or "and service" in t or "geography" in t):
                continue
            ym = re.search(r"(20\d{2})", title)
            year = int(ym.group(1)) if ym else 0
            uuid = None
            for dist in ds.get("distribution", []) or []:
                for key in ("accessURL", "downloadURL"):
                    m = re.search(r"/dataset/([0-9a-fA-F-]{36})/", dist.get(key, "") or "")
                    if m:
                        uuid = m.group(1)
                        break
                if uuid:
                    break
            if uuid and (best is None or year > best[0]):
                best = (year, uuid)
    if best:
        _CMS_UUID_CACHE["uuid"], _CMS_UUID_CACHE["year"] = best[1], best[0] or None
        return best[1], (best[0] or None)
    return None, None


def fetch_cms_medicare(npi: str, prof: ProviderProfile, override_uuid: str = "") -> None:
    uuid, year = discover_cms_dataset_uuid(override_uuid)
    if not uuid:
        prof.notes.append(
            "CMS: could not auto-discover the 'by Provider' dataset UUID. Pass "
            "--cms-dataset-uuid <uuid> (from the data.cms.gov dataset page).")
        return
    url = CMS_DATA_API.format(uuid=uuid)
    rows = _get(url, params={"filter[Rndrng_NPI]": npi, "size": 5}, timeout=40)
    if not rows or not isinstance(rows, list):
        prof.notes.append("CMS: no Medicare utilization row for this NPI (may not bill "
                          "Medicare Part B FFS, or year not yet released).")
        return
    row = None
    for r in rows:
        if str(r.get("Rndrng_NPI", "")).strip() == str(npi):
            row = r
            break
    if row is None:
        sample = rows[0] if rows else {}
        npis_seen = [str(r.get("Rndrng_NPI", "")) for r in rows[:5]]
        print(f"    [warn] CMS: filter returned {len(rows)} row(s), none matching NPI {npi}. "
              f"NPIs in response: {npis_seen}. First-row columns: {list(sample.keys())[:12]}",
              file=sys.stderr)
        prof.notes.append("CMS: no exact NPI match in the Medicare 'by Provider' dataset "
                          "(provider may not bill Medicare Part B FFS).")
        return

    prof.sources_used.append("CMS Medicare Physician & Other Practitioners")
    prof.medicare_data_year = year

    def _num(*keys, cast=float):
        for k in keys:
            if k in row and str(row[k]).strip() not in ("", "None"):
                try:
                    return cast(float(row[k]))
                except (ValueError, TypeError):
                    pass
        return None

    prof.medicare_beneficiaries = _num("Tot_Benes", cast=int)
    prof.medicare_total_services = _num("Tot_Srvcs")
    prof.medicare_total_payment = _num("Tot_Mdcr_Pymt_Amt")
    prof.medicare_drug_beneficiaries = _num("Drug_Tot_Benes", cast=int)
    prof.medicare_medical_beneficiaries = _num("Med_Tot_Benes", cast=int)
    prof.medicare_provider_type = str(row.get("Rndrng_Prvdr_Type", "") or row.get("Provider_Type", ""))


# ----------------------------------------------------------------------------
# Census ACS area wealth + geocoding
# ----------------------------------------------------------------------------
_CENSUS_CACHE: dict[str, Any] = {}
_CENSUS_VARS = "NAME,B19013_001E,B19301_001E,B25077_001E"


def census_for_zip(zip5: str, state: str = ""):
    if not zip5:
        return None
    fips = _STATE_FIPS.get((state or "").strip().upper(), "")
    cache_key = f"{fips}:{zip5}"
    if cache_key in _CENSUS_CACHE:
        return _CENSUS_CACHE[cache_key]
    last_raw = None
    for year in CENSUS_YEARS_TO_TRY:
        attempts = [{"get": _CENSUS_VARS, "for": f"zip code tabulation area:{zip5}"}]
        if fips:
            attempts.append({"get": _CENSUS_VARS,
                             "for": f"zip code tabulation area:{zip5}",
                             "in": f"state:{fips}"})
        for params in attempts:
            if CENSUS_API_KEY:
                params["key"] = CENSUS_API_KEY
            raw = _get(CENSUS_BASE.format(year=year), params=params, timeout=30, expect="text")
            if raw:
                last_raw = (year, raw.strip()[:200])
            if not raw or not raw.lstrip().startswith("["):
                continue
            try:
                data = json.loads(raw)
            except Exception:  # noqa: BLE001
                continue
            if isinstance(data, list) and len(data) >= 2:
                rec = dict(zip(data[0], data[1]))

                def _int(v):
                    try:
                        iv = int(float(v))
                        return iv if iv >= 0 else None
                    except (TypeError, ValueError):
                        return None

                out = {"year": year,
                       "median_household_income": _int(rec.get("B19013_001E")),
                       "per_capita_income": _int(rec.get("B19301_001E")),
                       "median_home_value": _int(rec.get("B25077_001E"))}
                _CENSUS_CACHE[cache_key] = out
                return out
    _CENSUS_CACHE[cache_key] = None
    if last_raw:
        print(f"    [warn] Census: no usable ACS row for ZCTA {zip5} "
              f"(last try {last_raw[0]}): {last_raw[1]}", file=sys.stderr)
    else:
        print(f"    [warn] Census: every ACS request for ZCTA {zip5} returned nothing "
              f"(network error or query rejected).", file=sys.stderr)
    return None


def enrich_area_wealth(prof: ProviderProfile) -> None:
    if not CENSUS_API_KEY:
        prof.notes.append("Census: area income/home value need a (free) Census API key. "
                          "Get one at https://api.census.gov/data/key_signup.html and set "
                          "it as the CENSUS_API_KEY environment variable.")
        return
    used = False
    for a in prof.addresses:
        info = census_for_zip(a.zip5, a.state)
        if info:
            a.area_median_household_income = info["median_household_income"]
            a.area_per_capita_income = info["per_capita_income"]
            a.area_median_home_value = info["median_home_value"]
            a.census_year = info["year"]
            used = True
    if used:
        prof.sources_used.append("U.S. Census ACS 5-year")


def census_geocode(addr: Address) -> None:
    oneline = addr.one_line()
    if not oneline:
        return
    data = _get(CENSUS_GEOCODER, params={"address": oneline,
                "benchmark": "Public_AR_Current", "format": "json"}, timeout=30)
    try:
        c = data["result"]["addressMatches"][0]["coordinates"]
        addr.lat, addr.lng = float(c["y"]), float(c["x"])
    except (TypeError, KeyError, IndexError, ValueError):
        pass


def google_geocode(addr: Address) -> bool:
    """Precise geocode via Google (the key already covers the Geocoding API)."""
    if not GOOGLE_API_KEY:
        return False
    oneline = addr.one_line()
    if not oneline:
        return False
    data = _get("https://maps.googleapis.com/maps/api/geocode/json",
                params={"address": oneline, "key": GOOGLE_API_KEY}, timeout=25)
    try:
        g = data["results"][0]["geometry"]["location"]
        addr.lat, addr.lng = float(g["lat"]), float(g["lng"])
        return True
    except (TypeError, KeyError, IndexError, ValueError):
        return False


# ----------------------------------------------------------------------------
# Imagery
# ----------------------------------------------------------------------------
def static_map_b64(lat: float, lng: float) -> Optional[str]:
    if GOOGLE_API_KEY:
        gurl = (f"https://maps.googleapis.com/maps/api/staticmap?center={lat},{lng}"
                f"&zoom=16&size=640x320&scale=2&markers=color:red%7C{lat},{lng}"
                f"&key={GOOGLE_API_KEY}")
        b = fetch_image_b64(gurl)
        if b:
            return b
    osm = (f"{OSM_STATICMAP}?center={lat},{lng}&zoom=16&size=640x320"
           f"&markers={lat},{lng},red-pushpin")
    return fetch_image_b64(osm)


def enrich_imagery(prof: ProviderProfile) -> None:
    used = False
    for a in prof.addresses:
        if not a.is_office:
            continue
        if a.lat is None or a.lng is None:
            if not google_geocode(a):
                census_geocode(a)
        if a.lat is None or a.lng is None:
            continue
        a.map_link = f"https://www.openstreetmap.org/?mlat={a.lat}&mlon={a.lng}#map=17/{a.lat}/{a.lng}"
        if not a.map_data_uri:
            mb = static_map_b64(a.lat, a.lng)
            if mb:
                a.map_data_uri = mb
                used = True
        if GOOGLE_API_KEY and not a.street_view_data_uri:
            # Pass the address (not raw lat/lng) so Street View tends to face the
            # premises rather than point off down the street.
            sv_loc = urllib.parse.quote_plus(a.one_line() or f"{a.lat},{a.lng}")
            sv = fetch_image_b64(
                f"https://maps.googleapis.com/maps/api/streetview?size=640x400&fov=80"
                f"&location={sv_loc}&return_error_code=true&key={GOOGLE_API_KEY}")
            if sv:
                a.street_view_data_uri = sv
                used = True
        if GOOGLE_API_KEY and not a.satellite_data_uri:
            # Zoomed aerial: shows the building, parking, and surrounding development
            # so you can judge whether the location fits a concierge practice.
            sat = fetch_image_b64(
                f"https://maps.googleapis.com/maps/api/staticmap?center={a.lat},{a.lng}"
                f"&zoom=17&size=640x400&scale=2&maptype=satellite"
                f"&markers=color:red%7C{a.lat},{a.lng}&key={GOOGLE_API_KEY}")
            if sat:
                a.satellite_data_uri = sat
                used = True
    if used:
        prof.sources_used.append("Geocoding + embedded map/Street View/aerial imagery")


# ----------------------------------------------------------------------------
# Google Places (rating, website, photos) - searches by physician NAME
# ----------------------------------------------------------------------------
def google_places_enrich(prof: ProviderProfile) -> None:
    if not GOOGLE_API_KEY:
        prof.notes.append("Google: set GOOGLE_MAPS_API_KEY to add an aggregate Google "
                          "rating, website, and building photos / Street View.")
        return
    loc = next((a for a in prof.addresses if a.purpose == "LOCATION"), None) or \
        (prof.addresses[0] if prof.addresses else None)
    if not loc:
        return

    field_mask = ("places.id,places.displayName,places.formattedAddress,places.rating,"
                  "places.userRatingCount,places.websiteUri")

    name = prof.full_name
    cred = prof.credential or ""
    city = loc.city or ""
    st = loc.state or ""
    # Search the way a person does: doctor NAME + credential + city/state first.
    queries = [
        f"{name} {cred} {city} {st}".strip(),
        f"{name} {prof.primary_taxonomy} {city} {st}".strip(),
        f"{name} {city} {st}".strip(),
        " ".join(filter(None, [prof.organization_name, loc.line1, city, st])),
    ]

    print(f"    [info] Google Places: trying name-based queries for {name}", file=sys.stderr)
    place = None
    last_resp_empty = True
    for q in queries:
        if not q:
            continue
        resp = _post("https://places.googleapis.com/v1/places:searchText",
                     json_body={"textQuery": q, "maxResultCount": 5},
                     headers={"X-Goog-Api-Key": GOOGLE_API_KEY,
                              "X-Goog-FieldMask": field_mask})
        places = (resp or {}).get("places") or []
        if not places:
            continue
        last_resp_empty = False
        rated = [p for p in places if p.get("rating") is not None]
        place = rated[0] if rated else places[0]
        if rated:
            break

    if not place:
        if last_resp_empty:
            prof.notes.append("Google Places: no listing matched this physician by name "
                              "(the doctor may not have a Google Business listing).")
        return

    prof.sources_used.append("Google Places")
    if place.get("rating") is not None:
        prof.reviews.append(ReviewSource(
            source="Google", rating=place.get("rating"),
            review_count=place.get("userRatingCount"),
            url=f"https://www.google.com/maps/place/?q=place_id:{place.get('id','')}"))
    else:
        prof.notes.append("Google Places matched a listing but it has no rating yet.")
    if place.get("websiteUri") and not prof.website:
        prof.website = place["websiteUri"]
    # We deliberately do not copy the listing's coordinates onto the office address,
    # nor pull its user-uploaded photos (often decor/random snapshots, not the
    # building). All imagery is anchored to the registered practice address below
    # so the Street View, aerial, and map agree on the same location.


# ----------------------------------------------------------------------------
# Web scraping: reviews, board certification, recognition
# ----------------------------------------------------------------------------
def _page_text_and_jsonld(html: str):
    jsonld = []
    if _HAVE_BS4:
        try:
            soup = BeautifulSoup(html, "html.parser")
            for s in soup.find_all("script", type="application/ld+json"):
                try:
                    jsonld.append(json.loads(s.string or ""))
                except Exception:  # noqa: BLE001
                    pass
            for tag in soup(["script", "style", "noscript"]):
                tag.decompose()
            text = soup.get_text(" ", strip=True)
        except Exception:  # noqa: BLE001
            text = html
    else:
        text = re.sub(r"<[^>]+>", " ", html)
    return text, jsonld


def _aggregate_rating_from_jsonld(jsonld_objs) -> Optional[ReviewSource]:
    def walk(o):
        if isinstance(o, dict):
            if "aggregateRating" in o and isinstance(o["aggregateRating"], dict):
                ar = o["aggregateRating"]
                try:
                    rating = float(ar.get("ratingValue"))
                except (TypeError, ValueError):
                    rating = None
                cnt = ar.get("reviewCount") or ar.get("ratingCount")
                try:
                    cnt = int(cnt)
                except (TypeError, ValueError):
                    cnt = None
                if rating is not None:
                    return rating, cnt
            for v in o.values():
                res = walk(v)
                if res:
                    return res
        elif isinstance(o, list):
            for v in o:
                res = walk(v)
                if res:
                    return res
        return None

    for obj in jsonld_objs:
        res = walk(obj)
        if res:
            return ReviewSource(source="Website (schema.org)", rating=res[0],
                                review_count=res[1], note="auto-extracted")
    return None


def _ratings_from_text(text: str) -> Optional[ReviewSource]:
    m = re.search(r"(\d(?:\.\d)?)\s*(?:out of|/)\s*5(?:\D{0,40}?(\d{1,4})\s+reviews?)?", text)
    if not m:
        m = re.search(r"(\d(?:\.\d)?)\s*stars?\D{0,40}?(\d{1,4})\s+reviews?", text)
    if m:
        try:
            rating = float(m.group(1))
        except ValueError:
            return None
        cnt = None
        if m.lastindex and m.lastindex >= 2 and m.group(2):
            try:
                cnt = int(m.group(2))
            except ValueError:
                cnt = None
        if 0 <= rating <= 5:
            return ReviewSource(source="Website (text)", rating=rating,
                                review_count=cnt, note="auto-extracted; verify")
    return None


def _find_certs_and_recognition(text: str):
    certs, recog = set(), set()
    for pat in _CERT_PATTERNS:
        for m in re.finditer(pat, text, flags=re.IGNORECASE):
            snippet = re.sub(r"\s+", " ", m.group(0)).strip()
            if 4 < len(snippet) < 120:
                certs.add(snippet.title())
    for pat in _RECOGNITION_PATTERNS:
        for m in re.finditer(pat, text, flags=re.IGNORECASE):
            snippet = re.sub(r"\s+", " ", m.group(0)).strip()
            if 3 < len(snippet) < 80:
                recog.add(snippet.title())
    return sorted(certs)[:8], sorted(recog)[:8]


def discover_website(prof: ProviderProfile) -> None:
    if prof.website:
        return
    q = urllib.parse.quote_plus(f"{prof.full_name} {prof.primary_taxonomy} "
                                f"{prof.addresses[0].city if prof.addresses else ''} official website")
    prof.notes.append(f"Website not auto-found. Lookup: https://duckduckgo.com/?q={q}")


def analyze_website_with_llm(prof: ProviderProfile, page_text: str) -> bool:
    """Read the homepage with Claude and extract structured practice info.
    Returns True if it populated fields, False to fall back to keyword matching."""
    if not ANTHROPIC_API_KEY:
        prof.notes.append("Website analysis: set ANTHROPIC_API_KEY to identify the practice "
                          "type, services, insurances, and recognitions by actually reading "
                          "the site (instead of crude keyword matching).")
        return False
    snippet = re.sub(r"\s+", " ", page_text)[:12000]
    instructions = (
        "You are analyzing a medical provider's website to help assess it as a "
        "concierge-medicine acquisition target. Using ONLY what the page states or clearly "
        "implies, return STRICT JSON (no markdown, no prose) with these keys: "
        '"practice_type" (short label, e.g. "Med spa / aesthetics", "Concierge internal '
        'medicine", "Primary care"), "summary" (one sentence on what the practice does), '
        '"services" (list of specific services), "insurances" (list of accepted plans; [] if '
        'cash-pay or none stated), "accepts_insurance" (true/false/null), '
        '"board_certifications" (list, each naming the specific board if stated, else []), '
        '"recognitions" (list of specific awards/recognitions with source or year if stated, '
        "else []). If something is not stated, use [] or null. Never invent.\n\n"
        f"PAGE TEXT:\n{snippet}"
    )
    resp = _post("https://api.anthropic.com/v1/messages",
                 json_body={"model": LLM_MODEL, "max_tokens": 1024,
                            "messages": [{"role": "user", "content": instructions}]},
                 headers={"x-api-key": ANTHROPIC_API_KEY,
                          "anthropic-version": "2023-06-01",
                          "content-type": "application/json"})
    if not resp:
        return False
    try:
        out = "".join(b.get("text", "") for b in resp.get("content", [])
                      if b.get("type") == "text").strip()
        out = re.sub(r"^```(?:json)?\s*|\s*```$", "", out).strip()
        data = json.loads(out)
    except Exception:  # noqa: BLE001
        print("    [warn] LLM website analysis: could not parse JSON response.", file=sys.stderr)
        return False

    def _strlist(v, n):
        return [str(x).strip() for x in v if str(x).strip()][:n] if isinstance(v, list) else []

    prof.practice_type = str(data.get("practice_type") or "").strip()
    prof.practice_summary = str(data.get("summary") or "").strip()
    prof.website_services = _strlist(data.get("services"), 30)
    prof.website_insurances = _strlist(data.get("insurances"), 30)
    prof.board_certifications = _strlist(data.get("board_certifications"), 12)
    prof.recognitions = _strlist(data.get("recognitions"), 12)
    prof.sources_used.append(f"Website analysis ({LLM_MODEL})")
    return True


def scrape_website(prof: ProviderProfile) -> None:
    if not prof.website:
        return
    html = _get(prof.website, expect="text", timeout=20)
    if not html:
        return
    text, jsonld = _page_text_and_jsonld(html)
    if not text:
        return
    prof.sources_used.append("Provider website (scraped)")
    low = text.lower()

    # Preferred path: let the model read the page and tell us what the practice is.
    # Falls back to keyword matching only when there's no Anthropic key / the call fails.
    if not analyze_website_with_llm(prof, text):
        prof.website_insurances = sorted({kw for kw in INSURANCE_KEYWORDS if kw in low})
        prof.website_services = sorted({kw for kw in SERVICE_KEYWORDS if kw in low})
        certs, recog = _find_certs_and_recognition(low)
        for c in certs:
            if c not in prof.board_certifications:
                prof.board_certifications.append(c)
        for r in recog:
            if r not in prof.recognitions:
                prof.recognitions.append(r)

    rev = _aggregate_rating_from_jsonld(jsonld) or _ratings_from_text(low)
    if rev:
        rev.url = prof.website
        prof.reviews.append(rev)


# ----------------------------------------------------------------------------
# Orchestration
# ----------------------------------------------------------------------------
def research_npi(npi: str, *, cms_uuid: str = "", do_google: bool = True,
                 do_scrape: bool = True) -> ProviderProfile:
    npi = re.sub(r"\D", "", str(npi))
    prof = ProviderProfile(npi=npi, retrieved_at=dt.datetime.now().isoformat(timespec="seconds"))
    if len(npi) != 10:
        prof.notes.append("Invalid NPI: must be 10 digits.")
        return prof

    print(f"[{npi}] NPPES ...")
    fetch_nppes(npi, prof)
    if not prof.full_name:
        return prof
    print(f"[{npi}] CMS Medicare ...")
    fetch_cms_medicare(npi, prof, override_uuid=cms_uuid)
    print(f"[{npi}] Census area wealth ...")
    enrich_area_wealth(prof)
    if do_google:
        print(f"[{npi}] Google Places ...")
        google_places_enrich(prof)
    print(f"[{npi}] Geocoding + imagery ...")
    enrich_imagery(prof)
    discover_website(prof)
    if do_scrape:
        print(f"[{npi}] Website scrape ...")
        scrape_website(prof)
    if not prof.reviews:
        prof.notes.append("No aggregate rating could be auto-extracted. If the doctor has a "
                          "Google listing, confirm Places API (New) is enabled and the key is set.")
    return prof


def viability_signals(prof: ProviderProfile) -> dict:
    loc = next((a for a in prof.addresses if a.purpose == "LOCATION"), None) or \
        (prof.addresses[0] if prof.addresses else None)
    return {
        "office_count": len([a for a in prof.addresses if a.is_office]),
        "area_median_household_income": loc.area_median_household_income if loc else None,
        "area_median_home_value": loc.area_median_home_value if loc else None,
    }


# ----------------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------------
def _profile_for_json(prof: ProviderProfile) -> dict:
    d = asdict(prof)
    for a in d.get("addresses", []):
        n = len(a.get("photo_data_uris") or [])
        a["photo_data_uris"] = f"<{n} embedded photo(s)>" if n else []
        if a.get("street_view_data_uri"):
            a["street_view_data_uri"] = "<embedded>"
        if a.get("satellite_data_uri"):
            a["satellite_data_uri"] = "<embedded>"
        if a.get("map_data_uri"):
            a["map_data_uri"] = "<embedded>"
    return d


def write_json(prof: ProviderProfile, outdir: str) -> str:
    path = os.path.join(outdir, f"{prof.npi}.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(_profile_for_json(prof), f, indent=2, ensure_ascii=False)
    return path


def _esc(s: Any) -> str:
    return (str(s) if s is not None else "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def write_html(prof: ProviderProfile, outdir: str) -> str:
    css = """
    body{font-family:Segoe UI,Arial,sans-serif;color:#1b1b1b;margin:0;background:#f4f6fa}
    .wrap{max-width:1000px;margin:0 auto;padding:24px}
    .card{background:#fff;border:1px solid #e1e5ee;border-radius:10px;padding:24px;margin:0 0 22px;box-shadow:0 1px 3px rgba(0,0,0,.05)}
    h1{font-size:21px;margin:0 0 4px} h2{font-size:15px;color:#1F3864;border-bottom:2px solid #1F3864;padding-bottom:4px;margin:24px 0 10px}
    h3{font-size:13px;margin:14px 0 6px;color:#33415c}
    .sub{color:#5a6577;font-size:13px;margin:0 0 14px}
    table{border-collapse:collapse;width:100%;font-size:13px;margin:6px 0}
    td,th{border:1px solid #e1e5ee;padding:6px 9px;text-align:left;vertical-align:top}
    th{background:#f0f3fa;color:#33415c}
    th.key{width:230px}
    .pill{display:inline-block;background:#eaf0fb;color:#1F3864;border-radius:12px;padding:2px 10px;margin:2px 4px 2px 0;font-size:12px}
    .office{border:1px solid #e8ebf2;border-radius:8px;padding:12px;margin:10px 0;background:#fafbfe}
    .imgs{display:flex;flex-wrap:wrap;gap:10px;margin-top:8px}
    .imgs figure{margin:0} .imgs img{height:170px;border-radius:6px;border:1px solid #ddd;display:block}
    .imgs figcaption{font-size:11px;color:#7a8295;margin-top:3px}
    a{color:#2557b8;text-decoration:none} a:hover{text-decoration:underline}
    .note{font-size:12px;color:#7a8295}
    .kpis{display:flex;flex-wrap:wrap;gap:12px;margin:10px 0 4px}
    .kpi{background:#f7f9fd;border:1px solid #e1e5ee;border-radius:8px;padding:10px 14px;min-width:150px}
    .kpi .v{font-size:18px;font-weight:600;color:#1F3864} .kpi .l{font-size:11px;color:#6b7488;text-transform:uppercase;letter-spacing:.3px}
    """
    sig = viability_signals(prof)

    def money(v):
        return f"${v:,}" if isinstance(v, int) else "—"

    def avg_rating():
        rs = [r.rating for r in prof.reviews if r.rating is not None]
        return round(sum(rs) / len(rs), 1) if rs else None

    P = [f"<!doctype html><html><head><meta charset='utf-8'>"
         f"<title>{_esc(prof.full_name)} — NPI {_esc(prof.npi)}</title>"
         f"<style>{css}</style></head><body><div class='wrap'>"]

    P.append("<div class='card'>")
    P.append(f"<h1>{_esc(prof.full_name)} {_esc(prof.credential)}</h1>")
    P.append(f"<p class='sub'>NPI {_esc(prof.npi)} · {_esc(prof.primary_taxonomy)} · "
             f"report generated {dt.datetime.now():%Y-%m-%d %H:%M}</p>")
    if prof.practice_type:
        P.append(f"<p class='sub'><b>Practice type:</b> {_esc(prof.practice_type)}"
                 f"{(' — ' + _esc(prof.practice_summary)) if prof.practice_summary else ''}</p>")

    ar = avg_rating()
    grating = next((r for r in prof.reviews if r.source == "Google" and r.rating is not None), None)
    kpis = [("Years in practice*", prof.years_in_practice_proxy or "—"),
            ("Offices", sig["office_count"]),
            ("Area median HH income", money(sig["area_median_household_income"])),
            ("Median home value", money(sig["area_median_home_value"])),
            ("Medicare beneficiaries", prof.medicare_beneficiaries if prof.medicare_beneficiaries is not None else "—"),
            ("Google rating", f"{grating.rating} ★ ({grating.review_count})" if grating else "—")]
    P.append("<div class='kpis'>")
    for label, val in kpis:
        P.append(f"<div class='kpi'><div class='v'>{_esc(val)}</div><div class='l'>{_esc(label)}</div></div>")
    P.append("</div>")

    P.append("<h2>Identity &amp; registration</h2><table>")
    for k, v in [("Enumeration date", prof.enumeration_date), ("Last NPPES update", prof.last_updated),
                 ("Gender", prof.gender), ("Sole proprietor", prof.sole_proprietor),
                 ("Organization", prof.organization_name), ("Licenses", ", ".join(prof.licenses)),
                 ("Specializations", ", ".join(prof.specializations))]:
        if v:
            P.append(f"<tr><th class='key'>{_esc(k)}</th><td>{_esc(v)}</td></tr>")
    P.append("</table>")

    if prof.medicare_beneficiaries is not None or prof.medicare_total_payment is not None:
        yr = f" ({prof.medicare_data_year})" if prof.medicare_data_year else ""
        P.append(f"<h2>Medicare profile{yr}</h2><table>")
        for k, v in [("Provider type", prof.medicare_provider_type),
                     ("Total beneficiaries", prof.medicare_beneficiaries),
                     ("Total services", prof.medicare_total_services),
                     ("Total Medicare payment", money(int(prof.medicare_total_payment)) if prof.medicare_total_payment else None),
                     ("Beneficiaries (medical)", prof.medicare_medical_beneficiaries),
                     ("Beneficiaries (drug)", prof.medicare_drug_beneficiaries)]:
            if v not in (None, ""):
                P.append(f"<tr><th class='key'>{_esc(k)}</th><td>{_esc(v)}</td></tr>")
        P.append("</table>")

    P.append("<h2>Office locations, area wealth &amp; imagery</h2>")
    for a in prof.addresses:
        if not a.is_office:
            continue
        P.append("<div class='office'>")
        P.append(f"<h3>{_esc(a.one_line())}{(' · ' + _esc(a.phone)) if a.phone else ''}</h3>")
        P.append("<table>"
                 f"<tr><th class='key'>Area median household income</th><td>{money(a.area_median_household_income)}</td></tr>"
                 f"<tr><th class='key'>Area per-capita income</th><td>{money(a.area_per_capita_income)}</td></tr>"
                 f"<tr><th class='key'>Area median home value</th><td>{money(a.area_median_home_value)}</td></tr>"
                 "</table>")
        imgs = []
        for u in a.photo_data_uris:
            imgs.append((u, "Office photo (Google)"))
        if a.street_view_data_uri:
            imgs.append((a.street_view_data_uri, "Street View"))
        if a.satellite_data_uri:
            imgs.append((a.satellite_data_uri, "Aerial view"))
        if a.map_data_uri:
            imgs.append((a.map_data_uri, "Location map"))
        if imgs:
            P.append("<div class='imgs'>")
            for src, cap in imgs:
                P.append(f"<figure><img src='{src}' alt='{_esc(cap)}'><figcaption>{_esc(cap)}</figcaption></figure>")
            P.append("</div>")
        elif a.map_link:
            P.append(f"<p class='note'>Map: <a href='{_esc(a.map_link)}' target='_blank'>view location on OpenStreetMap</a></p>")
        P.append("</div>")
    mailing = [a for a in prof.addresses if not a.is_office]
    if mailing:
        P.append("<p class='note'>Mailing: " + "; ".join(_esc(a.one_line()) for a in mailing) + "</p>")

    P.append("<h2>Web presence</h2><table>")
    if prof.website:
        P.append(f"<tr><th class='key'>Website</th><td><a href='{_esc(prof.website)}' target='_blank'>{_esc(prof.website)}</a></td></tr>")
    if prof.website_services:
        P.append("<tr><th class='key'>Services offered</th><td>"
                 + "".join(f"<span class='pill'>{_esc(s)}</span>" for s in prof.website_services) + "</td></tr>")
    if prof.website_insurances:
        P.append("<tr><th class='key'>Insurances accepted</th><td>"
                 + "".join(f"<span class='pill'>{_esc(s)}</span>" for s in prof.website_insurances) + "</td></tr>")
    P.append("</table>")

    P.append("<h2>Reviews &amp; ratings</h2>")
    rated = [r for r in prof.reviews if r.rating is not None]
    if rated:
        P.append("<table><tr><th class='key'>Source</th><th>Rating</th><th>Reviews</th></tr>")
        for r in rated:
            cnt = r.review_count if r.review_count is not None else "—"
            P.append(f"<tr><th class='key'>{_esc(r.source)}</th>"
                     f"<td>{_esc(r.rating)} ★</td><td>{_esc(cnt)}</td></tr>")
        if ar is not None and len(rated) > 1:
            P.append(f"<tr><th class='key'>Average (all sources)</th>"
                     f"<td><b>{_esc(ar)} ★</b></td><td>—</td></tr>")
        P.append("</table>")
    else:
        P.append("<p class='note'>No aggregate rating could be auto-extracted from public sources.</p>")

    P.append("<h2>Board certification &amp; recognition</h2>")
    if prof.board_certifications or prof.recognitions:
        P.append("<table>")
        if prof.board_certifications:
            P.append("<tr><th class='key'>Board certification (found)</th><td>"
                     + "".join(f"<span class='pill'>{_esc(c)}</span>" for c in prof.board_certifications)
                     + "</td></tr>")
        if prof.recognitions:
            P.append("<tr><th class='key'>Recognition / awards (found)</th><td>"
                     + "".join(f"<span class='pill'>{_esc(r)}</span>" for r in prof.recognitions)
                     + "</td></tr>")
        P.append("</table>")
        P.append("<p class='note'>Auto-extracted from the provider's website / public pages; verify.</p>")
    else:
        P.append("<p class='note'>No board-certification or recognition text was found on the "
                 "provider's website / public pages.</p>")

    if prof.notes:
        P.append("<h2>Notes &amp; data gaps</h2><ul class='note'>")
        for n in prof.notes:
            P.append(f"<li>{_esc(n)}</li>")
        P.append("</ul>")
    P.append(f"<p class='note'>Sources used: {_esc(', '.join(prof.sources_used) or 'none')}. "
             f"*Years in practice is a proxy (time since NPI enumeration).</p>")
    P.append("</div></div></body></html>")

    path = os.path.join(outdir, f"{prof.npi}.html")
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(P))
    return path


def open_in_chrome(path: str) -> None:
    """Open the report in Chrome (falls back to the default browser)."""
    uri = Path(path).resolve().as_uri()
    for exe in (r"C:\Program Files\Google\Chrome\Application\chrome.exe",
                r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe"):
        if os.path.exists(exe):
            webbrowser.register("chrome", None, webbrowser.BackgroundBrowser(exe))
            webbrowser.get("chrome").open(uri)
            return
    webbrowser.open(uri)


# ----------------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Look up one physician by NPI and open a self-contained HTML report in Chrome.")
    ap.add_argument("npi", nargs="?", help="A 10-digit NPI. If omitted, you'll be prompted.")
    ap.add_argument("--json", action="store_true",
                    help="Also write the raw JSON record alongside the report.")
    ap.add_argument("--cms-dataset-uuid", default="",
                    help="Override the CMS 'by Provider' dataset UUID if auto-discovery fails.")
    ap.add_argument("--no-google", action="store_true", help="Skip Google Places enrichment.")
    ap.add_argument("--no-scrape", action="store_true", help="Skip website/review scraping.")
    args = ap.parse_args(argv)

    npi = args.npi
    if not npi:
        npi = input("Enter the 10-digit NPI number to research: ").strip()

    outdir = tempfile.mkdtemp(prefix="npi_scout_")
    prof = research_npi(npi, cms_uuid=args.cms_dataset_uuid,
                        do_google=not args.no_google, do_scrape=not args.no_scrape)
    html = write_html(prof, outdir)
    if args.json:
        write_json(prof, outdir)
    open_in_chrome(html)
    print(f"\nDone. Opened report in Chrome:\n  {html}")
    if not prof.full_name:
        print("  (No NPPES record — check the NPI.)")


if __name__ == "__main__":
    main()
