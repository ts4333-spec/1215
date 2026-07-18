# 표준 라이브러리
import os
import re
import io
import json
import time
import html
import datetime
import logging
import sqlite3
import threading
import math
from string import Template
from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
from typing import Any, Dict, List, Optional, Set
from urllib.parse import quote_plus, urljoin
import xml.etree.ElementTree as ET

# 서드파티 라이브러리
import requests
from requests.adapters import HTTPAdapter, Retry
from bs4 import BeautifulSoup
import pandas as pd
import streamlit as st
from dotenv import load_dotenv
from openai import OpenAI
import gspread
from oauth2client.service_account import ServiceAccountCredentials
from pymarc import Record, Field, MARCWriter, Subfield           #✅ mrc 다운로드를 위해 requirements에 pymarc 추가해야함


class MarcBuilder:
    def __init__(self):
        self.rec = Record(to_unicode=True, force_utf8=True)
        self.lines: list[str] = []

    # 컨트롤필드(001–008)
    def add_ctl(self, tag: str, data: str):
        if not data:
            return
        self.rec.add_field(Field(tag=tag, data=str(data)))
        self.lines.append(f"={tag}  {data}")

    # 데이터필드(020/041/245/260/300/490/500/700/90010 …)
    def add(self, tag: str, ind1: str, ind2: str, subfields: list[tuple[str, str]]):
        sf = [(c, v) for c, v in subfields if (v or "") != ""]
        if not sf:
            return

        # ✅ 인디케이터 자동 보정 (백슬래시 → 공백)
        ind1 = " " if not ind1 or ind1 == "\\" else ind1
        ind2 = " " if not ind2 or ind2 == "\\" else ind2

        self.rec.add_field(Field(
            tag=tag,
            indicators=[ind1, ind2],
            subfields=[Subfield(c, v) for c, v in sf]
        ))

        parts = "".join(f"${c}{v}" for c, v in sf)
        self.lines.append(f"={tag}  {ind1}{ind2}{parts}")

    def mrk_text(self) -> str:
        return "\n".join(self.lines)

# Global meta store to avoid NameError
meta_all = {}
OPENAI_CHAT_COMPLETIONS = "https://api.openai.com/v1/chat/completions"
DEFAULT_MODEL = "gpt-4o-mini"

LOGGER_NAME = "isbn2marc"
logger = logging.getLogger(LOGGER_NAME)
if not logger.handlers:
    _handler = logging.StreamHandler()   # Streamlit 콘솔에도 찍히지만, 기본은 WARNING 이상만
    _fmt = logging.Formatter("%(levelname)s:%(name)s: %(message)s")
    _handler.setFormatter(_fmt)
    logger.addHandler(_handler)
logger.setLevel(logging.WARNING)  # 기본은 조용히


# Streamlit 디버그 토글 (없으면 False)
if "debug_mode" not in st.session_state:
    st.session_state["debug_mode"] = False
def _apply_log_level():
    logger.setLevel(logging.DEBUG if st.session_state["debug_mode"] else logging.WARNING)

# === Debug collector ===
CURRENT_DEBUG_LINES: list[str] = []
def dbg(*args):
    """조용히 디버그 라인을 수집 + logger로도 남김(레벨=DEBUG)."""
    from datetime import datetime
    msg = " ".join(str(a) for a in args)
    stamp = datetime.now().strftime("%H:%M:%S")
    line = f"[{stamp}] {msg}"
    CURRENT_DEBUG_LINES.append(line)
    logger.debug(msg)

def dbg_err(*args):
    """에러성 로그도 수집."""
    from datetime import datetime
    msg = " ".join(str(a) for a in args)
    stamp = datetime.now().strftime("%H:%M:%S")
    line = f"[{stamp}] ERROR: {msg}"
    CURRENT_DEBUG_LINES.append(line)
    logger.debug(msg)



# =========================
# 🔧 HTTP 세션 (재시도/UA/타임아웃 기본값)
# =========================
def _get_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({
        "User-Agent": "Mozilla/5.0 (compatible; isbn2marc/1.0; +https://local)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Encoding": "gzip, deflate",
        "Connection": "keep-alive",
    })
    retries = Retry(
        total=4, connect=2, read=3, backoff_factor=0.7,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=["GET"], raise_on_status=False
    )
    adapter = HTTPAdapter(max_retries=retries, pool_connections=10, pool_maxsize=10)
    s.mount("https://", adapter)
    s.mount("http://", adapter)
    return s

SESSION = _get_session()

# =========================
# 🔐 Secrets / Env
# =========================
OPENAI_API_KEY = os.getenv("OPENAI_API_KEY") or st.secrets.get("OPENAI_API_KEY", "")
ALADIN_TTB_KEY = os.getenv("ALADIN_TTB_KEY") or st.secrets.get("ALADIN_TTB_KEY", "")
NLK_CERT_KEY   = os.getenv("NLK_CERT_KEY")   or st.secrets.get("NLK_CERT_KEY", "")

# 🔐 Secrets / Env (통합)
ALADIN_TTB_KEY = (
    os.getenv("ALADIN_TTB_KEY")
    or st.secrets.get("ALADIN_TTB_KEY")
    or (st.secrets.get("aladin") or {}).get("ttbkey", "")
)

# 호환용 별칭(여기서 한 번에 정리)
aladin_key = ALADIN_TTB_KEY
ALADIN_KEY = ALADIN_TTB_KEY
openai_key = OPENAI_API_KEY
ttbkey     = ALADIN_TTB_KEY
DEFAULT_MODEL = (st.secrets.get("openai", {}) or {}).get("model") or os.getenv("OPENAI_MODEL") or "gpt-4o-mini"
model = DEFAULT_MODEL              # 별칭

# 맨 위 어딘가 (OPENAI_API_KEY 선언 이후)
try:
    from openai import OpenAI
    _client = OpenAI(api_key=OPENAI_API_KEY, timeout=10) if OPENAI_API_KEY else None
except Exception:
    _client = None


# ===== 환경변수 로드 =====
load_dotenv()
ALADIN_KEY = os.getenv("ALADIN_TTB_KEY")
OPENAI_KEY = os.getenv("OPENAI_API_KEY")
client = OpenAI(api_key=OPENAI_KEY)

def fetch_aladin_data(isbn13: str):
    isbn13 = isbn13.strip().replace("-", "")

    try:
        api_data = aladin_lookup_by_api(isbn13, ALADIN_TTB_KEY)
    except Exception as e:
        dbg(f"[ERROR] 알라딘 API 실패: {e}")
        api_data = None

    try:
        detail = crawl_aladin_fallback(isbn13)
    except Exception as e:
        dbg(f"[ERROR] 알라딘 상세 크롤링 실패: {e}")
        detail = {}
    
    return {"api": (api_data.extra if api_data else {}), "detail": detail}





# ===== ISDS 언어코드 매핑 =====
ISDS_LANGUAGE_CODES = {
    'kor': '한국어', 'eng': '영어', 'jpn': '일본어', 'chi': '중국어',
    'rus': '러시아어', 'ara': '아랍어', 'fre': '프랑스어', 'ger': '독일어',
    'ita': '이탈리아어', 'spa': '스페인어', 'por': '포르투갈어', 'tur': '터키어',
    'und': '알 수 없음'
}
ALLOWED_CODES = set(ISDS_LANGUAGE_CODES.keys()) - {"und"}

# ===== 공통 유틸: GPT 응답 파싱(코드 + 이유) =====
def _extract_code_and_reason(content, code_key="$h"):
    code, reason, signals = "und", "", ""
    lines = [l.strip() for l in (content or "").splitlines() if l.strip()]
    for ln in lines:
        if ln.startswith(f"{code_key}="):
            code = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#reason="):
            reason = ln.split("=", 1)[1].strip()
        elif ln.lower().startswith("#signals="):
            signals = ln.split("=", 1)[1].strip()
    return code, reason, signals

# ===== GPT 판단 함수 (원서; 일반) =====
def gpt_guess_original_lang(title, category, publisher, author="", original_title=""):
    prompt = f"""
    아래 도서의 원서 언어(041 $h)를 ISDS 코드로 추정해줘.
    가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

    도서정보:
    - 제목: {title}
    - 원제: {original_title or "(없음)"}
    - 분류: {category}
    - 출판사: {publisher}
    - 저자: {author}

    지침:
    - 국가/지역을 언어로 곧바로 치환하지 말 것.
    - 저자 국적·주 집필 언어·최초 출간 언어를 우선 고려.
    - 불확실하면 임의 추정 대신 'und' 사용.

    출력형식(정확히 이 2~3줄):
    $h=[ISDS 코드]
    #reason=[짧게 근거 요약]
    #signals=[잡은 단서들, 콤마로](선택)
    """.strip()
    try:
        resp = client.chat.completions.create(
            model="gpt-4o",
            messages=[{"role": "system","content":"사서용 언어 추정기"},
                      {"role":"user","content":prompt}],
            temperature=0
        )
        content = (resp.choices[0].message.content or "").strip()
        code, reason, signals = _extract_code_and_reason(content, "$h")
        if code not in ALLOWED_CODES:
            code = "und"
        dbg(f"🧭 [GPT 근거] $h={code}")
        if reason: dbg(f"🧭 [이유] {reason}")
        if signals: dbg(f"🧭 [단서] {signals}")
        return code
    except Exception as e:
        dbg_error(f"GPT 오류: {e}")
        return "und"

# ===== GPT 판단 함수 (본문) =====
def gpt_guess_main_lang(title, category, publisher):
    prompt = f"""
    아래 도서의 본문 언어(041 $a)를 ISDS 코드로 추정.
    가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

    입력:
    - 제목: {title}
    - 분류: {category}
    - 출판사: {publisher}

    지침:
    - '본문 언어'는 이 자료의 **현시본(Manifestation)** 언어다.
    - 저자 국적, 원작 언어, 시리즈 원산지 등 **원작 관련 단서 사용 금지**.
    - 카테고리에 '국내도서'가 있거나, 제목에 **한글이 1자라도** 포함되면 반드시 kor.
    - 허용 코드 밖이거나 불확실하면 'und'.

    출력형식:
    $a=[ISDS 코드]
    #reason=[짧게 근거 요약]
    #signals=[잡은 단서들, 콤마로](선택)
    """.strip()
    try:
        resp = client.chat.completions.create(
            model="gpt-4o",
            messages=[{"role": "system","content":"사서용 본문 언어 추정기"},
                      {"role":"user","content":prompt}],
            temperature=0
        )
        content = (resp.choices[0].message.content or "").strip()
        code, reason, signals = _extract_code_and_reason(content, "$a")
        if code not in ALLOWED_CODES:
            code = "und"
        st.write(f"🧭 [GPT 근거] $a={code}")
        if reason: st.write(f"🧭 [이유] {reason}")
        if signals: st.write(f"🧭 [단서] {signals}")
        return code
    except Exception as e:
        st.error(f"GPT 오류: {e}")
        return "und"

# ===== GPT 판단 함수 (신규) — 저자 기반 원서 언어 추정 =====
def gpt_guess_original_lang_by_author(author, title="", category="", publisher=""):
    prompt = f"""
    저자 정보를 중심으로 원서 언어(041 $h)를 ISDS 코드로 추정.
    가능한 코드: kor, eng, jpn, chi, rus, fre, ger, ita, spa, por, tur

    입력:
    - 저자: {author}
    - (참고) 제목: {title}
    - (참고) 분류: {category}
    - (참고) 출판사: {publisher}

    지침:
    - 저자 국적·주 집필 언어·대표 작품 원어를 우선.
    - 국가=언어 단순 치환 금지.
    - 불확실하면 'und'.

    출력형식:
    $h=[ISDS 코드]
    #reason=[짧게 근거 요약]
    #signals=[잡은 단서들, 콤마로](선택)
    """.strip()
    try:
        resp = client.chat.completions.create(
            model="gpt-4o",
            messages=[{"role":"system","content":"저자 기반 원서 언어 추정기"},
                      {"role":"user","content":prompt}],
            temperature=0
        )
        content = (resp.choices[0].message.content or "").strip()
        code, reason, signals = _extract_code_and_reason(content, "$h")
        if code not in ALLOWED_CODES:
            code = "und"
        st.write(f"🧭 [저자기반 근거] $h={code}")
        if reason: st.write(f"🧭 [이유] {reason}")
        if signals: st.write(f"🧭 [단서] {signals}")
        return code
    except Exception as e:
        st.error(f"GPT(저자기반) 오류: {e}")
        return "und"

# ===== 언어 감지 함수들 =====
def detect_language_by_unicode(text):
    text = re.sub(r'[\s\W_]+', '', text or "")
    if not text:
        return 'und'
    c = text[0]
    if '\uac00' <= c <= '\ud7a3': return 'kor'
    if '\u3040' <= c <= '\u30ff': return 'jpn'
    if '\u4e00' <= c <= '\u9fff': return 'chi'
    if '\u0600' <= c <= '\u06FF': return 'ara'
    if '\u0e00' <= c <= '\u0e7f': return 'tha'
    return 'und'

def override_language_by_keywords(text, initial_lang):
    text = (text or "").lower()
    if initial_lang == 'chi' and re.search(r'[\u3040-\u30ff]', text): return 'jpn'
    if initial_lang in ['und', 'eng']:
        if "spanish" in text or "español" in text: return "spa"
        if "italian" in text or "italiano" in text: return "ita"
        if "french" in text or "français" in text: return "fre"
        if "portuguese" in text or "português" in text: return "por"
        if "german" in text or "deutsch" in text: return "ger"
        if any(ch in text for ch in ['é','è','ê','à','ç','ù','ô','â','î','û']): return "fre"
        if any(ch in text for ch in ['ñ','á','í','ó','ú']): return "spa"
        if any(ch in text for ch in ['ã','õ']): return "por"
    return initial_lang

def detect_language(text):
    lang = detect_language_by_unicode(text)
    return override_language_by_keywords(text, lang)

def detect_language_from_category(text):
    words = re.split(r'[>/\s]+', text or "")
    for w in words:
        if "일본" in w: return "jpn"
        if "중국" in w: return "chi"
        if "영미" in w or "영어" in w or "아일랜드" in w: return "eng"
        if "프랑스" in w: return "fre"
        if "독일" in w or "오스트리아" in w: return "ger"
        if "러시아" in w: return "rus"
        if "이탈리아" in w: return "ita"
        if "스페인" in w: return "spa"
        if "포르투갈" in w: return "por"
        if "튀르키예" in w or "터키" in w: return "tur"
    return None

# ===== 카테고리 토크나이즈 & 판정 유틸 =====
def tokenize_category(text: str):
    if not text:
        return []
    t = re.sub(r'[()]+', ' ', text)
    raw = re.split(r'[>/\s]+', t)
    tokens = []
    for w in raw:
        w = w.strip()
        if not w:
            continue
        if '/' in w and w.count('/') <= 3 and len(w) <= 20:
            tokens.extend([p for p in w.split('/') if p])
        else:
            tokens.append(w)
    lower_tokens = tokens + [w.lower() for w in tokens if any('A'<=ch<='Z' or 'a'<=ch<='z' for ch in w)]
    return lower_tokens

def has_kw_token(tokens, kws):
    s = set(tokens)
    return any(k in s for k in kws)

def trigger_kw_token(tokens, kws):
    s = set(tokens)
    for k in kws:
        if k in s:
            return k
    return None

def is_literature_top(category_text: str) -> bool:
    return "소설/시/희곡" in (category_text or "")

def is_literature_category(category_text: str) -> bool:
    tokens = tokenize_category(category_text or "")
    ko_hits = ["문학", "소설", "시", "희곡"]
    en_hits = ["literature", "fiction", "novel", "poetry", "poem", "drama", "play"]
    return has_kw_token(tokens, ko_hits) or has_kw_token(tokens, en_hits)

def is_nonfiction_override(category_text: str) -> bool:
    """
    문학처럼 보여도 '역사/지역/전기/사회과학/에세이' 등 비문학 지표가 있으면 비문학으로 강제.
    단, 문학 최상위(소설/시/희곡)면 '과학/기술'은 제외(SF 보호).
    """
    tokens = tokenize_category(category_text or "")
    lit_top = is_literature_top(category_text or "")

    ko_nf_strict = ["역사","근현대사","서양사","유럽사","전기","평전",
                    "사회","정치","철학","경제","경영","인문","에세이","수필"]
    en_nf_strict = ["history","biography","memoir","politics","philosophy",
                    "economics","science","technology","nonfiction","essay","essays"]

    sci_keys = ["과학","기술"]; sci_keys_en = ["science","technology"]

    k = trigger_kw_token(tokens, ko_nf_strict) or trigger_kw_token(tokens, en_nf_strict)
    if k:
        dbg(f"🔎 [판정근거] 비문학 키워드 발견: '{k}'")
        return True

    if not lit_top:
        k2 = trigger_kw_token(tokens, sci_keys) or trigger_kw_token(tokens, sci_keys_en)
        if k2:
            dbg(f"🔎 [판정근거] 비문학 최상위 추정 & '{k2}' 발견 → 비문학 오버라이드")
            return True

    if lit_top:
        dbg("🔎 [판정근거] 문학 최상위 감지: '과학/기술'은 오버라이드에서 제외(SF 보호).")
    return False

# ===== 기타 유틸 =====
def strip_ns(tag): return tag.split('}')[-1] if '}' in tag else tag

# ===== 웹 크롤링 =====
def crawl_aladin_fallback(isbn13):
    url = f"https://www.aladin.co.kr/shop/wproduct.aspx?ISBN={isbn13}"
    headers = {"User-Agent": "Mozilla/5.0"}
    try:
        res = requests.get(url, headers=headers, timeout=10)
        soup = BeautifulSoup(res.text, "html.parser")

        # --- 원제 블록 (기존) ---
        original = soup.select_one("div.info_original")
        lang_info = soup.select_one("div.conts_info_list1")

        # --- 카테고리 텍스트 (기존) ---
        category_text = ""
        categories = soup.select("div.conts_info_list2 li")
        for cat in categories:
            category_text += cat.get_text(separator=" ", strip=True) + " "

        detected_lang = ""
        if lang_info and "언어" in lang_info.text:
            if "Japanese" in lang_info.text:
                detected_lang = "jpn"
            elif "Chinese" in lang_info.text:
                detected_lang = "chi"
            elif "English" in lang_info.text:
                detected_lang = "eng"

        original_title = original.text.strip() if original else ""

        # --- 🔥 원어 저자명 추출  ---
        original_author = ""

        for script in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(script.string or "")
            except Exception:
                continue

            # Book 타입만 관심
            if not (isinstance(data, dict) and data.get("@type") == "Book"):
                continue

            author = data.get("author")
            name_field = ""

            # author가 dict 인 경우
            if isinstance(author, dict):
                name_field = author.get("name", "") or ""
            # author가 list 인 경우 (여러 명)
            elif isinstance(author, list):
                names = []
                for a in author:
                    if isinstance(a, dict):
                        nm = a.get("name", "")
                        if nm:
                            names.append(nm)
                name_field = ", ".join(names)

            if not name_field:
                continue

            # 예: "싱클레어 B. 퍼거슨, Sinclair Buchanan Ferguson"
            parts = [p.strip() for p in name_field.split(",") if p.strip()]
            original_author = ""

            # 국내도서는 "한글명, 원어표기" 구조 → 두 번째 요소가 원어명
            if len(parts) >= 2:
                cand = parts[1]
                # 안전장치: 한글이면 버림
                if not re.search(r"[가-힣]", cand):
                    original_author = cand


        return {
            "original_title": original_title,
            "original_author": original_author,  # ⭐ 여기!
            "subject_lang": detect_language_from_category(category_text) or detected_lang,
            "category_text": category_text,
        }

    except Exception as e:
        dbg_error(f"❌ 크롤링 중 오류 발생: {e}")
        return {}


# ===== 결과 조정(충돌 해소) =====
def reconcile_language(candidate, fallback_hint=None, author_hint=None):
    """
    candidate: 1차 GPT 결과
    fallback_hint: 카테고리/원제 규칙에서 얻은 힌트(예: 'ger')
    author_hint: 저자 기반 GPT 결과
    """
    if author_hint and author_hint != "und" and author_hint != candidate:
        st.write(f"🔁 [조정] 저자기반({author_hint}) ≠ 1차({candidate}) → 저자기반 우선")
        return author_hint
    if fallback_hint and fallback_hint != "und" and fallback_hint != candidate:
        if candidate in {"ita","fre","spa","por"}:
            if fallback_hint == "eng":
                # 영어 힌트는 흔히 과대검출 — GPT 결과 유지
                return candidate
            # 영어가 아니라면(예: ger vs fre) 규칙 힌트를 우선
            st.write(f"🔁 [조정] 규칙힌트({fallback_hint}) vs 1차({candidate}) → 규칙힌트 우선")
            return fallback_hint
            
    return candidate

# ===== $h 우선순위 결정 (저자 기반 보정 + 근거 로깅 포함) =====


def determine_h_language(
    title: str,
    original_title: str,
    category_text: str,
    publisher: str,
    author: str,
    subject_lang: str
) -> str:
    """
    문학: 카테고리/웹 → (부족시) GPT → (여전히 불확실) 저자 기반 보정
    비문학: GPT → (부족시) 카테고리/웹 → (여전히 불확실) 저자 기반 보정
    """
    lit_raw = is_literature_category(category_text)
    nf_override = is_nonfiction_override(category_text)
    is_lit_final = lit_raw and not nf_override

    # 사람이 읽기 쉬운 설명
    if lit_raw and not nf_override:
        dbg("📘 [판정] 이 자료는 문학(소설/시/희곡 등) 성격이 뚜렷합니다.")
    elif lit_raw and nf_override:
        dbg("📘 [판정] 겉보기에는 문학이지만, '역사·에세이·사회과학' 등 비문학 요소가 함께 보여 최종적으로는 비문학으로 처리될 수 있습니다.")
    elif not lit_raw and nf_override:
        dbg("📘 [판정] 문학적 단서는 없고, 비문학(역사·사회·철학 등) 성격이 강합니다.")
    else:
        dbg("📘 [판정] 문학/비문학 판단 단서가 약해 추가 판단이 필요합니다.")

    rule_from_original = detect_language(original_title) if original_title else "und"
    lang_h = None
    author_hint = None

    if is_lit_final:
        # 문학: 1) 카테고리/웹 → 2) 원제 유니코드 → 3) GPT → 4) 저자 기반
        lang_h = subject_lang or rule_from_original
        dbg(f"📘 [설명] (문학 흐름) 1차 후보: {lang_h or 'und'}")
        if not lang_h or lang_h == "und":
            dbg("📘 [설명] (문학 흐름) GPT 보완 시도…")
            lang_h = gpt_guess_original_lang(title, category_text, publisher, author, original_title)
            dbg(f"📘 [설명] (문학 흐름) GPT 결과: {lang_h}")
        if (not lang_h or lang_h == "und") and author:
            dbg("📘 [설명] (문학 흐름) 원제 없음/애매 → 저자 기반 보정 시도…")
            author_hint = gpt_guess_original_lang_by_author(author, title, category_text, publisher)
            dbg(f"📘 [설명] (문학 흐름) 저자 기반 결과: {author_hint}")
    else:
        # 비문학: 1) GPT → 2) 카테고리/웹 → 3) 원제 유니코드 → 4) 저자 기반
        dbg("📘 [설명] (비문학 흐름) GPT 선행 판단…")
        lang_h = gpt_guess_original_lang(title, category_text, publisher, author, original_title)
        dbg(f"📘 [설명] (비문학 흐름) GPT 결과: {lang_h or 'und'}")
        if not lang_h or lang_h == "und":
            lang_h = subject_lang or rule_from_original
            dbg(f"📘 [설명] (비문학 흐름) 보조 규칙 적용 → 후보: {lang_h or 'und'}")
        if author and (not lang_h or lang_h == "und"):
            dbg("📘 [설명] (비문학 흐름) 원제 없음/애매 → 저자 기반 보정 시도…")
            author_hint = gpt_guess_original_lang_by_author(author, title, category_text, publisher)
            dbg(f"📘 [설명] (비문학 흐름) 저자 기반 결과: {author_hint}")

    # 충돌 조정
    fallback_hint = subject_lang or rule_from_original
    lang_h = reconcile_language(candidate=lang_h, fallback_hint=fallback_hint, author_hint=author_hint)
    dbg("📘 [결과] 조정 후 원서 언어(h) =", lang_h)

    return (lang_h if lang_h in ALLOWED_CODES else "und") or "und"

# ===== 국내도서 여부 가드 =====
def is_domestic_category(category_text: str) -> bool:
    return "국내도서" in (category_text or "")

# ===== KORMARC 태그 생성기 =====
# ===== KORMARC 태그 생성기 =====
def get_kormarc_tags(item, detail):
    """
    item : 알라딘 API dict (item.extra)
    detail : 크롤링 dict (crawl_aladin_fallback 결과)
    """
    item = item or {}
    detail = detail or {}

    title = item.get("title", "") or ""
    publisher = item.get("publisher", "") or ""
    author = item.get("author", "") or ""

    # subInfo → 원서명
    subinfo = (item.get("subInfo") or {}) or {}
    original_title = subinfo.get("originalTitle", "") or ""
    original_title = html.unescape(original_title)

    # 크롤링 원서명 보완
    if not original_title:
        original_title = detail.get("original_title", "") or ""

    subject_lang = detail.get("subject_lang")
    category_text = item.get("categoryText", "") or detail.get("category_text", "") or ""

    try:
        # ---- $a: 본문 언어 ----
        # 1) 규칙 기반 1차 감지
        lang_a = detect_language(title)
        dbg("📘 [DEBUG] 규칙 기반 1차 lang_a =", lang_a)

        # 2) 강한 가드: '국내도서'면 kor로 고정
        if is_domestic_category(category_text):
            dbg("📘 [판정] 카테고리에 '국내도서' 감지 → $a=kor(강한 가드)")
            lang_a = "kor"

        # 3) GPT 보조: und/eng일 때만 호출
        if lang_a in ("und", "eng"):
            dbg("📘 [설명] und/eng → GPT 보조로 본문 언어 재판정…")
            gpt_a = gpt_guess_main_lang(title, category_text, publisher)
            dbg(f"📘 [설명] GPT 판단 lang_a = {gpt_a}")
            if gpt_a in ALLOWED_CODES:
                lang_a = gpt_a
            else:
                lang_a = "und"

        # ---- $h: 원저 언어 ----
        dbg("📘 [DEBUG] 원제 감지됨:", bool(original_title), "| 원제:", original_title or "(없음)")
        dbg("📘 [DEBUG] 카테고리/크롤링 기반 lang_h 후보 =", subject_lang or "(없음)")

        lang_h = determine_h_language(
            title=title,
            original_title=original_title,
            category_text=category_text,
            publisher=publisher,
            author=author,
            subject_lang=subject_lang,
        )
        dbg("📘 [결과] 최종 원서 언어(h) =", lang_h)

        # ---- 태그 조합 ----
        if lang_h and lang_h != lang_a and lang_h != "und":
            tag_041 = f"041 $a{lang_a} $h{lang_h}"
        else:
            tag_041 = f"041 $a{lang_a}"

        # 번역서($h)가 아니면 041/546 둘 다 안 만듦
        if "$h" not in tag_041:
            return None, None, original_title

        # 번역서일 때만 546 생성
        tag_546 = generate_546_from_041_kormarc(tag_041)
        return tag_041, tag_546, original_title

    except Exception as e:
        dbg(f"📕 [ERROR] get_kormarc_tags 예외 발생: {e}")
        return f"📕 예외 발생: {e}", "", original_title


def _as_mrk_041(tag_041: str | None) -> str | None:
    """
    '041 $akor$hrus' → '=041  1\\$akor$hrus'
    (=041 / 041 접두와 중간 공백이 들어와도 정규화)
    """
    if not tag_041:
        return None
    s = tag_041.strip()
    # 앞의 '041' / '=041' 제거
    s = re.sub(r"^=?\s*041\s*", "", s)
    # 서브필드 사이 공백 제거
    s = re.sub(r"\s+", "", s)
    if not s.startswith("$a"):
        return None
    return f"=041  1\\{s}"

def _as_mrk_546(tag_546_text: str | None) -> str | None:
    """
    '러시아어원작을 한국어로 번역' → '=546  \\\\$a러시아어원작을 한국어로 번역'
    (이미 '=546'로 시작하면 그대로)
    """
    if not tag_546_text:
        return None
    t = tag_546_text.strip()
    if not t:
        return None
    if t.startswith("=546"):
        return t
    if t.startswith("$a"):
        return f"=546  \\\\{t}"
    return f"=546  \\\\$a{t}"



# =========================
# 저자 서명 필드 관련                   
# =========================

# 저자명    
USE_WIKIDATA = True
INCLUDE_ORIGINAL_NAME_IN_90010 = True     # 원어명 → 90010에 기록
USE_NLK_LOD_AUTH = True                 # NLK LOD 사용
PREFER_LOD_FIRST = True                 # LOD 먼저 시도 → 실패 시 Wikidata 폴백
RECORD_PROVENANCE_META = True           # 출처 메타 기록
_KOREAN_ONLY_RX = re.compile(r"^[가-힣\s·\u00B7]$")  # 외국인 이름 판정용(한글·중점 제외)


# ==== Aladin endpoints & HTTP defaults (global) ====
ALADIN_ITEMLOOKUP_URL = "https://www.aladin.co.kr/ttb/api/ItemLookUp.aspx"
# 검색 페이지(스크레이핑 백업용): query에 ISBN이나 서명 넣어 사용
ALADIN_SEARCH_URL = "https://www.aladin.co.kr/search/wsearchresult.aspx?SearchTarget=Book&SearchWord={query}"

# 공통 요청 헤더(봇 차단 회피 & 한글 검색 결과 안정화)
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8,en;q=0.7",
    "Cache-Control": "no-cache",
}
DEFAULT_TIMEOUT = 10  # seconds

# CSV 로드
def load_uploaded_csv(uploaded):
    import io
    content = uploaded.getvalue()
    last_err = None
    for enc in ("utf-8-sig", "utf-8", "cp949", "euc-kr"):
        try:
            text = content.decode(enc)
            return pd.read_csv(io.StringIO(text), engine="python", sep=None, dtype=str)
        except Exception as e:
            last_err = e
    raise RuntimeError(f"CSV 인코딩/파싱 실패: {last_err}")


def pick_non_hangul_label(labels: list[str]) -> str | None:
    cand = [x.strip() for x in (labels or []) if x and _script_rank(x.strip()) != 9]
    if not cand: return None
    return sorted(cand, key=_script_rank)[0]

SEPS = r"(?:,|·|/|・|&|\band\b|\b그리고\b|\b및\b)"

ROLE_ALIASES = {
    # author 계열
    "지은이":"author","저자":"author","글":"author","글쓴이":"author","집필":"author","원작":"author",
    "지음":"author","글작가":"author","스토리":"author",
    # translator 계열
    "옮긴이":"translator","옮김":"translator","역자":"translator","역":"translator","번역":"translator","역주":"translator","공역":"translator",
    # illustrator 계열
    "그림":"illustrator","그린이":"illustrator","삽화":"illustrator","일러스트":"illustrator","만화":"illustrator","작화":"illustrator","채색":"illustrator",
    # editor 등 (필요시)
    "엮음":"editor","엮은이":"editor","편집":"editor","편":"editor","편저":"editor","편집자":"editor",
    # 영문 혼입 대비
    "author":"author","writer":"author","story":"author",
    "translator":"translator","trans":"translator","translated":"translator",
    "illustrator":"illustrator","illus.":"illustrator","artist":"illustrator",
    "editor":"editor","ed.":"editor",
}

def normalize_role(token: str) -> str:
    """
    알라딘의 authorTypeName 등 역할명을 ROLE_ALIASES 기반으로 정규화.
    복합 표기(예: '글·그림', '지음/옮김')도 인식.
    """
    if not token:
        return "other"

    # 불필요한 괄호, 공백 제거
    t = re.sub(r"[()\[\]\s{}]", "", token.strip().lower())

    # 복합 표기(글·그림 / 글/그림 등) 분리
    parts = re.split(r"[·/・]", t)

    cats = set()
    for p in parts:
        p = p.strip()
        if not p:
            continue

        # ROLE_ALIASES 딕셔너리 직접 활용
        if p in ROLE_ALIASES:
            cats.add(ROLE_ALIASES[p])
        else:
            # 혹시 ROLE_ALIASES 키 일부가 포함된 경우도 잡기 (예: "일러스트레이터")
            for key, val in ROLE_ALIASES.items():
                if key in p:
                    cats.add(val)
                    break
            else:
                cats.add("other")

    # 우선순위: 옮긴이 > 지은이 > 그림 > 엮은이
    for pref in ("translator", "author", "illustrator", "editor"):
        if pref in cats:
            return pref

    return "other"


def strip_tail_role(name: str) -> tuple[str, str]:
    m = re.search(r"\(([^)]+)\)\s*$", name.strip())
    if not m:
        return name.strip(), "other"
    base = name[:m.start()].strip()
    return base, normalize_role(m.group(1))

def split_names(chunk: str) -> list[str]:
    if not chunk: return []
    chunk = re.sub(r"^\s*\([^)]*\)\s*", "", chunk.strip())  # 앞머리 괄호 역할 제거
    parts = re.split(rf"\s*{SEPS}\s*", chunk)
    return [p.strip() for p in parts if p and p.strip()]

def parse_people_flexible(author_str: str) -> dict:
    """
    핵심: 직전 이름 덩어리(last_names)를 기억했다가,
    바로 다음 토큰이 역할이면 그 이름들을 그 역할로 '재할당'한다.
    (예: '김연경 (옮긴이)'가 split되어 '김연경' 과 '(옮긴이)'로 떨어지는 경우 커버)
    """
    out = defaultdict(list)
    if not author_str:
        return out

    role_pattern = r"(\([^)]*\)|지은이|저자|글|글쓴이|집필|원작|엮음|엮은이|지음|글작가|스토리|옮긴이|옮김|역자|역|번역|역주|공역|그림|그린|삽화|일러스트|만화|편집|편|편저|편집자|author|writer|story|translator|trans|translated|editor|ed\.|illustrator|illus\.|artist)"
    tokens = [t.strip() for t in re.split(role_pattern, author_str) if t and t.strip()]

    current = "other"
    pending = []            # 역할 없는 이름 대기(앞에 이름, 뒤에 역할 나오는 케이스)
    last_names = []         # 방금 처리한 이름들
    last_assigned_to = None # last_names를 어디에 넣었는지 기억

    seen_real_role = False  # 🔥 author/translator/illustrator/editor를 한번이라도 봤는지

    def _assign(lst, cat):
        for x in lst:
            out[cat].append(x)

    for tok in tokens:
        role_cat = normalize_role(tok)

        # 🔥 순수 '(기획)', '(해설)' 같은 꼬리표는 통째로 무시
        if role_cat == "other":
            stripped = tok.strip()
            if stripped.startswith("(") and stripped.endswith(")"):
                inner = stripped[1:-1].strip()
                if any(kw in inner for kw in ("기획", "기획·구성", "기획/구성", "구성", "해설")):
                    # 이 토큰은 역할로도, 이름으로도 쓰지 않음
                    continue

        if role_cat != "other":
            # 🔥 진짜 역할(author/editor/illustrator/translator)이면 플래그 ON
            if role_cat in ("author", "translator", "illustrator", "editor"):
                seen_real_role = True

            # 1) 앞에서 이름만 나오고 아직 역할이 없었다면 → 이번 역할로 배정
            if pending:
                _assign(pending, role_cat)
                pending.clear()
                last_names = []  # pending은 과거 덩어리이므로 last_names 초기화
                last_assigned_to = None
            else:
                # 2) 바로 직전에 이름을 '현재 current'로 넣어둔 상태에서
                #    이번 토큰이 '(옮긴이)' 같은 '뒤꼬리 역할'이면 → 재할당
                if last_names and last_assigned_to:
                    # 기존 배정에서 제거
                    for x in last_names:
                        try:
                            out[last_assigned_to].remove(x)
                        except ValueError:
                            pass
                    # 새 역할로 배정
                    _assign(last_names, role_cat)
                    # 클리어
                    last_names = []
                    last_assigned_to = None

            current = role_cat
            continue

        # 이름 덩어리 처리
        names = split_names(tok)
        if not names:
            continue

        # 각 이름 단위로 '홍길동 (역)' 같은 뒤꼬리 꼬리표가 직접 붙어있으면 그걸로 우선 배정
        direct = []
        for raw in names:
            base, tail = strip_tail_role(raw)
            if tail != "other":
                out[tail].append(base)
                direct.append(base)

        # direct로 이미 처리된 것 제외
        remain = [n for n in names if n not in direct]
        if not remain:
            last_names = direct
            last_assigned_to = None
            continue

        if current != "other":
            _assign(remain, current)
            last_names = remain[:]      # 방금 넣은 걸 기억 (다음 토큰이 역할이면 재할당)
            last_assigned_to = current
        else:
            # 아직 역할이 없으면 보류 → 다음 역할 토큰에 배정
            pending.extend(remain)
            last_names = remain[:]      # 직후 역할 토큰이 오면 이들을 그 역할로 배정
            last_assigned_to = None

    # 🔥 루프 종료 후 pending 처리 로직 변경
    if pending:
        if seen_real_role:
            # ▶ 지은이/옮긴이/그림/엮은이 같은 '진짜 역할'이 한 번이라도 나왔으면
            #    기존처럼 author로 넣어줌 (김철수, 김영희 (지은이) 케이스 보호)
            _assign(pending, "author")
        else:
            # ▶ 기획/해설 등만 있고, 진짜 역할은 없었던 경우 → 몽땅 버림
            # dbg(f"[AUTHOR] 역할 없는 이름(기획/기타로 판단) → 무시: {pending}")
            pass

    # 중복 제거(역할별)
    for k, arr in out.items():
        seen = set(); uniq=[]
        for x in arr:
            if x not in seen:
                seen.add(x); uniq.append(x)
        out[k] = uniq

    return out


def _dedup(seq):
    seen=set(); out=[]
    for x in seq:
        if x not in seen:
            seen.add(x); out.append(x)
    return out

def extract_people_from_aladin(item: dict) -> dict:
    """
    알라딘 subInfo.authors 기반 저자 파싱.
    - 지은이(author)
    - 옮긴이(translator)
    - 그림(illustrator)
    - 엮은이(editor)
    - 기획/해설 등 기타 역할은 무시(people에 넣지 않음)
    """
    res = {"author": [], "translator": [], "illustrator": [], "editor": [], "other": []}

    if not item:
        return res

    sub = (item.get("subInfo") or {})
    arr = sub.get("authors")

    # ------------------------------
    # --- 구조화된 저자 리스트 사용 ---
    # ------------------------------
    if isinstance(arr, list) and arr:
        for a in arr:
            name = (a.get("authorName") or a.get("name") or "").strip()
            typ  = (a.get("authorTypeName") or a.get("authorType") or "").strip()
            if not name:
                continue

            # ------------------------------
            # 🔥 1) '기획' 계열 역할은 통째로 무시
            # ------------------------------
            typ_compact = re.sub(r"\s+", "", typ or "")
            if any(kw in typ_compact for kw in ("기획", "기획·구성", "기획/구성")):
                # 예: authorTypeName="기획"
                continue

            # 이름 자체가 "(기획)" 같은 꼬리표 포함하는 경우도 제거
            m = re.search(r"\(([^)]*)\)", name)
            if m and ("기획" in m.group(1)):
                continue

            # ------------------------------
            # 🔥 2) 이름 꼬리표 먼저 제거 (strip_tail_role)
            # ------------------------------
            base, tail = strip_tail_role(name)

            # ------------------------------
            # 🔥 3) 역할 분류 (normalize)
            # ------------------------------
            cat = normalize_role(typ)  # typ 기반 우선
            if tail != "other":
                cat = tail              # tail 역할 우선 적용

            # cat이 'other'이면 사람 버리기
            if cat == "other":
                continue

            res.setdefault(cat, []).append(base)

        # 중복 제거
        for k in list(res.keys()):
            res[k] = _dedup(res[k])

        return res

    # ----------------------------------------
    # --- fallback: 일반 문자열 AUTHOR 파싱 ---
    # ----------------------------------------
    parsed = parse_people_flexible(item.get("author") or "")

    # parse_people_flexible는 already dict 형태 반환
    for k, lst in parsed.items():
        if k in res:
            res[k].extend(lst)

    # dedup
    for k in list(res.keys()):
        res[k] = _dedup(res[k])

    return res


def build_700_from_people(people: dict, reorder_fn=None, aladin_item=None) -> list[str]:
    """
    people 딕셔너리(author, editor, illustrator, translator)를 기반으로
    700 필드를 역할 순서(지은이→엮은이→그림→옮긴이)로 생성
    """
    lines = []

    authors = people.get("author", [])
    edtrs   = people.get("editor", [])
    illus   = people.get("illustrator", [])
    trans   = people.get("translator", [])

    def reorder(name):
        return reorder_fn(name, aladin_item=aladin_item) if reorder_fn else name

    # 1️⃣ 지은이
    for a in authors:
        lines.append(f"=700  1\\$a{reorder(a)}")

    # 2️⃣ 엮은이
    for e in edtrs:
        lines.append(f"=700  1\\$a{reorder(e)}")

    # 3️⃣ 그림
    for i in illus:
        lines.append(f"=700  1\\$a{reorder(i)}")

    # 4️⃣ 옮긴이
    for t in trans:
        lines.append(f"=700  1\\$a{reorder(t)}")

    return lines




# === [PATCH] JSON 직렬화 헬퍼 추가 ===
def _jsonify(obj):
    """dict/list/set 안에 set이 섞여 있어도 JSON으로 저장 가능하게 변환"""
    if isinstance(obj, set):
        return sorted(obj)
    if isinstance(obj, dict):
        return {k: _jsonify(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_jsonify(v) for v in obj]
    return obj

def _ensure_name_bundle(d):
    if d is None:
        return {"native": set(), "roman": set(), "countries": set()}
    return {
        "native": set(d.get("native", [])),
        "roman": set(d.get("roman", [])),
        "countries": set(d.get("countries", [])),
    }


# 외국인 이름
_HANGUL_RE = re.compile(r"[가-힣]")

# 한글로 적힌 '서양식' 이름의 흔한 첫이름(음역) 목록
# 필요하면 점점 보태가면 됨
_WESTERN_GIVEN_KO = (
    "마이클","조지","제임스","존","데이비드","스티븐","스티브","에릭","에드워드",
    "리처드","로버트","찰스","윌리엄","벤자민","가브리엘","조슈아","알렉산더",
    "크리스토퍼","크리스천","대니얼","도널드","더글러스","프랭크","헨리","잭",
    "제이슨","제프리","조셉","케네스","래리","마크","매튜","니콜라스","폴",
    "피터","사무엘","스콧","토머스","앤드류","안토니오","카를","피에르","장",
    "프랑수아","가르시아","베르나르","기욤","가브리엘"
)

def _looks_western_korean_translit(name: str) -> bool:
    """한글 표기지만 서양식 개인이름(음역) 같은지 간단 추정"""
    parts = [p for p in name.strip().split() if p]
    if not parts:
        return False
    first = parts[0]
    return first in _WESTERN_GIVEN_KO

def _summarize_name_context_from_aladin(item: dict | None) -> str:
    if not item:
        return ""
    sub  = (item.get("subInfo") or {})
    seri = (item.get("seriesInfo") or {})
    pieces = []
    if (sub.get("originalTitle") or "").strip():
        pieces.append(f"originalTitle={(sub.get('originalTitle') or '').strip()}")
    if (item.get("categoryName") or "").strip():
        pieces.append(f"categoryName={(item.get('categoryName') or '').strip()}")
    if (item.get("publisher") or "").strip():
        pieces.append(f"publisher={(item.get('publisher') or '').strip()}")
    if (item.get("pubDate") or "").strip():
        pieces.append(f"pubDate={(item.get('pubDate') or '').strip()}")
    if (seri.get("seriesName") or "").strip():
        pieces.append(f"seriesName={(seri.get('seriesName') or '').strip()}")
    return " | ".join(pieces)

def reorder_name_by_lang(name: str, origin_lang_code: str | None) -> str:
    east_asian_langs = {"jpn", "chi", "zho"}
    western_langs    = {"eng", "fre", "ger", "spa", "ita", "rus","por","dut","nld"}

    s = (name or "").strip()
    if not s:
        return s

    # 먼저 CJK 문자면 그냥 두기 (원문이 일본어/중국어인 경우)
    if re.search(r"[\u3040-\u30FF\u3400-\u4DBF\u4E00-\u9FFF]", s):
        return s

    if origin_lang_code:
        code3 = origin_lang_code.strip().lower()
        if code3 in east_asian_langs:
            return s
        if code3 in western_langs:
            parts = s.split()
            if len(parts) == 2:
                return f"{parts[1]}, {parts[0]}"
            if len(parts) >= 3:
                family = parts[-1]
                given  = " ".join(parts[:-1])
                return f"{family}, {given}"
    # 코드 없으면 그냥 스크립트 기반만 적용 (CJK 아니면 뒤집기 or 그대로)
    parts = s.split()
    if len(parts) >= 2 and not re.search(r"[\u3040-\u30FF\u3400-\u4DBF\u4E00-\u9FFF]", s):
        family = parts[-1]
        given  = " ".join(parts[:-1])
        return f"{family}, {given}"
    return s



# =========================
# 🧠 OpenAI (아시아권 KEEP / 비아시아권 '성, 이름')
# =========================

LLM_SCHEMA = {
    "type": "json_schema",
    "json_schema": {
        "name": "NameOrderDecision",
        "strict": True,
        "schema": {
            "type": "object",
            "properties": {
                "action":  {"type": "string", "enum": ["REORDER", "KEEP"]},
                "result":  {"type": "string"},
                "reason":  {"type": "string"},
                "confidence": {"type": "number"}
            },
            "required": ["action", "result"]
        }
    }
}

SYSTEM_PROMPT = (
    "당신은 한국 도서관 KORMARC 700 필드용 이름 정렬 보조자입니다.\n"
    "입력은 '한글 표기' 저자명과 알라딘/위키데이터 메타 컨텍스트입니다.\n"
    "임무: 이름의 성·이름 순서를 판별하고, 필요 시 '성, 이름'으로 재배열하여 결과를 JSON으로만 응답합니다.\n"
    "\n"
    "[가정/근거 신호]\n"
    "- wikidata_country: 위키데이터 P27(시민권/국적)\n"
    "- wikidata_labels: 다국어 라벨(en/ja/zh/ru 등)\n"
    "- originalTitle: 원서명(로마자)\n"
    "- categoryName: 주제/지역 힌트(예: '영미', '프랑스 문학')\n"
    "\n"
    "[판별 우선순위]\n"
    "1) 한글 표기 이름이 성–이름 관습인 언어권(한국/중국/일본 등)으로 명백하면 KEEP.\n"
    "2) 그 외에는 wikidata_country/labels/originalTitle/categoryName를 근거로 일반적 관습을 추정:\n"
    "   - 다수 유럽/미주권: 기본 이름–성 → '성, 이름'으로 REORDER.\n"
    "   - 러시아/동유럽권: 이름–성 제공이 흔함 → REORDER.\n"
    "3) 단일 이름(모노님)은 KEEP.\n"
    "\n"
    "[예외/세부 규칙]\n"
    "- 스페인/포르투갈 복성(de, da, del, de la, dos, y 등) → 성 성, 이름 유지(예: '가르시아 마르케스, 가브리엘').\n"
    "- 네덜란드 접두사(van, van der, de 등)는 성의 일부로 처리(예: '반 고흐, 빈센트').\n"
    "- 하이픈 성/이름은 통째로 유지(예: '장-폴').\n"
    "- 러시아식 부칭(-비치/-브나/-오비치 등)은 이름 뒤에 두고, 성을 앞으로(예: '도스토옙스키, 표도르').\n"
    "- 베트남식은 통상 성–이름이므로 KEEP.\n"
    "- 인물이 단체/기관으로 보이면 KEEP.\n"
    "\n"
    "[출력 형식]\n"
    "JSON 한 줄만:\n"
    "{\"action\":\"KEEP|REORDER\",\"result\":\"<최종 표기>\",\"reason\":\"<근거>\",\"confidence\":0.0~1.0}\n"
    "※ REORDER 시 result는 반드시 '성, 이름'이어야 함. 근거에는 사용 신호(country/labels 등) 기재.\n"
)



def _is_mononym(h: str) -> bool:
    parts = [p for p in re.split(r"\s+", (h or "").strip()) if p]
    return len(parts) <= 1

@lru_cache(maxsize=4096)
def decide_name_order_via_llm(hangul_name: str, ctx_key: str = "") -> dict:
    """
    hangul_name: '앤 래드클리프' 같은 한글 표기
    ctx_key: 컨텍스트 요약 문자열(_summarize_name_context_from_aladin(...) 결과)
    """
    name = (hangul_name or "").strip()
    if not name:
        return {"action":"KEEP","result":"","reason":"empty","confidence":0.0}

    # 모노님은 바로 KEEP
    if len(name.split()) <= 1:
        return {"action":"KEEP","result":name,"reason":"mononym","confidence":0.9}

    # API 없으면 간단 폴백(2어절만 뒤집기)
    if not _client or not OPENAI_API_KEY:
        parts = name.split()
        if len(parts) == 2 and _HANGUL_RE.search(name):
            first, last = parts[0], parts[1]
            return {"action":"REORDER","result":f"{last}, {first}","reason":"fallback-no-client","confidence":0.4}
        return {"action":"KEEP","result":name,"reason":"fallback-keep","confidence":0.4}

    try:
        user_msg = f'이름: "{name}"\n컨텍스트: {ctx_key}'
        resp = _client.responses.create(
            model="gpt-4o-mini",
            instructions=SYSTEM_PROMPT,
            input=user_msg,
            response_format=LLM_SCHEMA,
            temperature=0
        )
        data = json.loads(resp.output_text)
        action = data.get("action","KEEP")
        result = (data.get("result") or name).strip()
        if action == "REORDER" and "," not in result and _HANGUL_RE.search(name):
            parts = name.split()
            if len(parts) == 2:
                first, last = parts[0], parts[1]
                result = f"{last}, {first}"
        return {"action": action, "result": result,
                "reason": data.get("reason",""), "confidence": data.get("confidence",0.75)}
    except Exception as e:
        parts = name.split()
        if len(parts) == 2 and _HANGUL_RE.search(name):
            first, last = parts[0], parts[1]
            return {"action":"REORDER","result":f"{last}, {first}","reason":f"fallback:{e}","confidence":0.4}
        return {"action":"KEEP","result":name,"reason":f"fallback-keep:{e}","confidence":0.4}

def reorder_hangul_name_for_700(
    name: str,
    *,
    aladin_item: dict | None = None,
    origin_lang_code: str | None = None
):
    """
    700 필드용 이름 재배열.
    - 기본 재배열 규칙은 reorder_name_by_lang()에 위임
    - origin_lang_code가 있을 때는 그 코드 기준으로 정렬
    - 코드가 없을 때만 LLM 폴백 사용
    """
    s = (name or "").strip()
    if not s:
        return s

    # 1) 언어 코드가 있으면 공통 로직 사용
    if origin_lang_code:
        return reorder_name_by_lang(s, origin_lang_code)

    # 2) 언어 코드가 없으면, 기존처럼 LLM에 맡김 (원하면 여기서도 helper만 쓰게 바꿔도 됨)
    ctx = _summarize_name_context_from_aladin(aladin_item)
    try:
        return decide_name_order_via_llm(s, ctx_key=ctx)["result"]
    except Exception:
        # LLM 실패 시에는 그냥 원문 그대로 반환
        return s


    # 2) fallback: LLM / 위키데이터 기반 추정 로직
    ctx = _summarize_name_context_from_aladin(aladin_item)
    return decide_name_order_via_llm(s, ctx_key=ctx)["result"]
    
    
def get_anycase(rec: dict, key: str):
    if not rec:
        return None
    key_norm = key.strip().upper()
    for k, v in rec.items():
        if (k or "").strip().upper() == key_norm:
            return v
    return None

# === NLK LOD (SPARQL) ===
_NLK_Lod_Endpoints = ["https://lod.nl.go.kr/sparql", "http://lod.nl.go.kr/sparql"]
_NLK_HEADERS = {
    "Accept": "application/sparql-results+json",
    "Content-Type": "application/x-www-form-urlencoded; charset=UTF-8",
    "User-Agent": "isbn2marc/1.0 (+local)"
}

def _nlk_sparql(query: str, timeout=(10, 60), retries=2, backoff=1.6):
    import time, requests
    last = None
    for ep in _NLK_Lod_Endpoints:
        for i in range(retries):
            try:
                r = SESSION.post(ep, data={"query": query, "format": "json"},
                                 headers=_NLK_HEADERS, timeout=timeout)
                r.raise_for_status()
                return ep, r.json()
            except Exception as e:
                last = (ep, e)
                if i < retries - 1:
                    time.sleep(backoff**(i+1))
                else:
                    break
    raise RuntimeError(f"NLK LOD 실패: {last[0]} :: {repr(last[1])}")

def _lod_search_persons_by_name_ko(name_ko: str, limit: int = 10):
    # 한국어 이름(부분일치)으로 nlon:Author 후보를 찾음
    safe = name_ko.replace('"', '\\"').strip()
    q = f"""
PREFIX nlon: <http://lod.nl.go.kr/ontology/>
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?person ?name WHERE {{
  ?person a nlon:Author ; foaf:name ?name .
  FILTER(LANG(?name)="ko")
  FILTER(REGEX(STR(?name), "{safe}", "i"))
}}
LIMIT {limit}
"""
    ep, data = _nlk_sparql(q)
    rows = data.get("results", {}).get("bindings", [])
    return ep, [{"person": r["person"]["value"], "name": r["name"]["value"]} for r in rows]

def _lod_get_all_names(person_uri: str):
    q = f"""
PREFIX foaf: <http://xmlns.com/foaf/0.1/>
SELECT ?name (LANG(?name) AS ?lang) WHERE {{
  <{person_uri}> foaf:name ?name .
}}
"""
    ep, data = _nlk_sparql(q)
    out = []
    for b in data.get("results", {}).get("bindings", []):
        out.append({"name": b["name"]["value"], "lang": b.get("lang", {}).get("value", "")})
    return ep, out

def get_original_name_via_lod(name_ko: str):
    """
    한국어 표기 '홍길동' → NLK LOD로 후보 URI 찾고 → 비한글 이름 1개 선택.
    반환: (원어명 또는 None, provenance_meta)
    """
    if not (USE_NLK_LOD_AUTH and name_ko.strip()):
        return None, None
    try:
        ep1, cands = _lod_search_persons_by_name_ko(name_ko, limit=10)
        if not cands:
            return None, {"source":"NLK LOD", "endpoint": ep1, "reason":"no candidates", "name_ko": name_ko}
        # 첫 후보로 상세 라벨 조회
        chosen = cands[0]
        ep2, names = _lod_get_all_names(chosen["person"])
        # 비한글 라벨 하나 고르기 (함수 pick_non_hangul_label 재사용)
        labels = [n["name"] for n in names]
        best = pick_non_hangul_label(labels)
        prov = {
            "source": "NLK LOD",
            "endpoint_search": ep1,
            "endpoint_fetch": ep2,
            "person_uri": chosen["person"],
            "matched_name_ko": chosen["name"],
            "candidates": cands[:3],
            "names_sample": names[:8]
        }
        return best, prov
    except Exception as e:
        return None, {"source":"NLK LOD", "error":repr(e), "name_ko":name_ko}


WD_SPARQL = "https://query.wikidata.org/sparql"

def get_original_name_via_wikidata(name_hint: str) -> str | None:
    """
    한글 표기(예: '표도르 도스토옙스키')를 받아 Wikidata에서
    비한글(원어) 라벨을 하나 골라 반환. 실패 시 None.
    """
    import re as _re
    name_hint = (name_hint or "").strip()
    if not name_hint:
        return None

    ck = f"wd-orig:{name_hint}"
    try:
        c = cache_get(ck)
        if isinstance(c, dict) and "orig" in c:
            return c["orig"]
    except Exception:
        pass

    qvars = [name_hint]
    if "옙" in name_hint:
        qvars.append(name_hint.replace("옙", "예"))
    if "예프" in name_hint:
        qvars.append(name_hint.replace("예프", "옙"))
    qvars.append(_re.sub(r"\s+", "", name_hint))

    hits = []
    for q in qvars:
        try:
            res = wikidata_search_ko(q, limit=10) or []
        except Exception:
            res = []
        hits.extend(res)
        if res:
            break

    if not hits:
        try:
            cache_set(ck, {"orig": None})
        except Exception:
            pass
        return None

    best = hits[0]
    labels = []
    if best.get("native"):
        labels.append(best["native"])
    if best.get("label_ru"):
        labels.append(best["label_ru"])
    if best.get("label_en"):
        labels.append(best["label_en"])

    orig = pick_non_hangul_label(labels)

    try:
        cache_set(ck, {"orig": orig})
    except Exception:
        pass
    return orig

def build_90010_from_wikidata(people: dict, include_translator: bool = False) -> list[str]:
    """
    Wrapper: prefer NLK LOD first, then Wikidata; returns 90010 lines only.
    """
    lines, _prov = build_90010_prefer_lod_then_wikidata_with_meta(people, include_translator=include_translator)
    return lines

_WD_API = "https://www.wikidata.org/w/api.php"
_WD_UA = {"User-Agent": "MARC-Auto/0.1 (edu; test)"}
_KO_WIKI_API = "https://ko.wikipedia.org/w/api.php"

def _get_qid_via_kowiki(title_ko: str):
    """ko.wikipedia에서 title로 wikibase_item(QID) 얻기"""
    try:
        r = SESSION.get(_KO_WIKI_API, headers=_WD_UA, params={
            "action":"query","titles":title_ko,"prop":"pageprops","ppprop":"wikibase_item","format":"json"
        }, timeout=(10,30))
        r.raise_for_status()
        data = r.json().get("query", {}).get("pages", {})
        for _, page in data.items():
            qid = page.get("pageprops", {}).get("wikibase_item")
            if qid:
                return qid
        return None
    except Exception:
        return None

def _wd_search_qid_ko(name: str, limit=10):
    try:
        r = SESSION.get(_WD_API, headers=_WD_UA, params={
            "action":"wbsearchentities","search":name,"language":"ko","uselang":"ko",
            "type":"item","limit":limit,"format":"json"
        }, timeout=(10,30))
        r.raise_for_status()
        arr = r.json().get("search", [])
        return arr[0]["id"] if arr else None
    except Exception:
        return None

def _wd_get_labels(qid: str, langs=("ru","en","ja","zh","ko")):
    try:
        r = SESSION.get(_WD_API, headers=_WD_UA, params={
            "action":"wbgetentities","ids":qid,"props":"labels|aliases",
            "languages":"|".join(langs),"format":"json"
        }, timeout=(10,30))
        r.raise_for_status()
        ent = r.json().get("entities", {}).get(qid, {})
        return ent.get("labels", {}), ent.get("aliases", {})
    except Exception:
        return {}, {}

def _simple_reorder_family_given(label: str):
    parts = (label or "").strip().split()
    if len(parts) == 2:
        return f"{parts[1]}, {parts[0]}"
    return label

_WD_API = "https://www.wikidata.org/w/api.php"
_WD_UA = {"User-Agent": "MARC-Auto/0.2 (edu; streamlit)"}
_KO_WIKI_API = "https://ko.wikipedia.org/w/api.php"

_WD_COUNTRY_TO_LANG = {
    "Q17": "ja",  # Japan
    "Q148": "zh", # China
    "Q159": "ru", # Russia
    "Q142": "fr", # France
    "Q183": "de", # Germany
    "Q29": "es",  # Spain
    "Q38": "it",  # Italy
    "Q145": "en", # UK
    "Q30": "en",  # USA
}
_DEFAULT_LANGS = ["ja","zh","ru","en","ko"]
_KOREAN_P27_QIDS = {"Q884","Q423","Q180"}
_EAST_ASIAN_P27 = {"Q17","Q148","Q884","Q423","Q865","Q864","Q14773"}

def _wd_get_p27_list(qid: str) -> list[str]:
    if not qid:
        return []
    try:
        r = SESSION.get(_WD_API, headers=_WD_UA, params={
            "action":"wbgetentities","ids":qid,"props":"claims","format":"json"
        }, timeout=(10,30))
        r.raise_for_status()
        ent = r.json().get("entities", {}).get(qid, {})
        out = []
        for stmt in ent.get("claims", {}).get("P27", []):
            try:
                out.append(stmt["mainsnak"]["datavalue"]["value"]["id"])
            except Exception:
                pass
        return out
    except Exception:
        return []

def _wd_is_korean_national(qid: str) -> bool:
    return any(c in _KOREAN_P27_QIDS for c in _wd_get_p27_list(qid))

def _wd_preferred_langs_for_qid(qid: str) -> list[str]:
    prefs = []
    for c in _wd_get_p27_list(qid):
        lang = _WD_COUNTRY_TO_LANG.get(c)
        if lang and lang not in prefs:
            prefs.append(lang)
    for x in _DEFAULT_LANGS:
        if x not in prefs:
            prefs.append(x)
    return prefs

def _wd_get_labels(qid: str, langs: tuple[str, ...] = ("ja","zh","ru","en","ko")):
    """라벨/별칭 조회 (언어 우선순위 지정 가능)"""
    try:
        r = SESSION.get(_WD_API, headers=_WD_UA, params={
            "action":"wbgetentities","ids":qid,"props":"labels|aliases",
            "languages":"|".join(langs),"format":"json"
        }, timeout=(10,30))
        r.raise_for_status()
        ent = r.json().get("entities", {}).get(qid, {})
        return ent.get("labels", {}), ent.get("aliases", {})
    except Exception:
        return {}, {}

def _get_qid_via_kowiki(title_ko: str):
    """ko.wikipedia에서 title로 wikibase_item(QID) 얻기"""
    try:
        r = SESSION.get(_KO_WIKI_API, headers=_WD_UA, params={
            "action":"query","titles":title_ko,"prop":"pageprops","ppprop":"wikibase_item","format":"json"
        }, timeout=(10,30))
        r.raise_for_status()
        data = r.json().get("query", {}).get("pages", {})
        for _, page in data.items():
            qid = page.get("pageprops", {}).get("wikibase_item")
            if qid:
                return qid
        return None
    except Exception:
        return None

def get_original_name_via_wikidata_rest(name_ko: str):
    qid = _wd_search_qid_ko(name_ko)
    if not qid:
        qid = _get_qid_via_kowiki(name_ko)
        if not qid:
            return None, {"source":"Wikidata(REST)", "reason":"no qid", "name_ko":name_ko}
        pref_langs = tuple(_wd_preferred_langs_for_qid(qid))
        labels, _ = _wd_get_labels(qid, langs=pref_langs)
        for lang in pref_langs:
            if lang in labels:
                val = labels[lang]["value"]
                if lang in ("en",) and " " in val.strip():
                    val = _simple_reorder_family_given(val)
                return val, {"source":"Wikidata(REST:ko-wiki)", "qid": qid, "lang": lang}
        for lang, obj in labels.items():
            return obj["value"], {"source":"Wikidata(REST:ko-wiki)", "qid": qid, "lang": lang}
        return None, {"source":"Wikidata(REST:ko-wiki)", "qid": qid, "reason":"no labels"}
    pref_langs = tuple(_wd_preferred_langs_for_qid(qid))
    labels, _ = _wd_get_labels(qid, langs=pref_langs)
    for lang in pref_langs:
        if lang in labels:
            val = labels[lang]["value"]
            if lang in ("en",) and " " in val.strip():
                val = _simple_reorder_family_given(val)
            return val, {"source":"Wikidata(REST)", "qid": qid, "lang": lang}
    for lang, obj in labels.items():
        return obj["value"], {"source":"Wikidata(REST)", "qid": qid, "lang": lang}
    return None, {"source":"Wikidata(REST)", "qid": qid, "reason":"no labels"}

def _ko_name_variants(name_ko: str) -> list[str]:
    """주어진 한글 인명에서 검색용 변이(표기 순서/띄어쓰기/옙·예프)를 생성."""
    name_ko = (name_ko or "").strip()
    out = set()
    if not name_ko:
        return []
    out.add(name_ko)
    # "성, 이름" → "이름 성"
    if "," in name_ko:
        parts = [p.strip() for p in name_ko.split(",")]
        if len(parts) == 2 and parts[0] and parts[1]:
            out.add(f"{parts[1]} {parts[0]}")
    # '옙'↔'예' / '예프'↔'옙' 변이
    seeds = list(out)
    for s in seeds:
        out.add(s.replace("옙", "예"))
        out.add(s.replace("예프", "옙"))
    # 공백 제거/추가 변이
    seeds = list(out)
    for s in seeds:
        out.add(s.replace(" ", ""))
    # 너무 많아지지 않게 상위 몇 개만
    return list(out)[:8]

def resolve_original_name_prefer_lod(name_ko: str):
    """
    Aladin에서 받은 한국어 저자명 그대로만 사용.
      1) NLK LOD → 성공 시 채택 (route=LOD)
      2) 기존 Wikidata 함수 → 성공 시 채택 (route=Wikidata, note=legacy)
      3) Wikidata REST → 최종 폴백 (route=Wikidata(REST))
    """
    key = (name_ko or "").strip()
    # 1) LOD
    try:
        val, prov = get_original_name_via_lod(key)
    except Exception as e:
        val, prov = (None, {"route":"LOD", "source":"NLK LOD", "error":repr(e), "key": key})
    if val:
        return val, {"route":"LOD", "key": key, **(prov or {})}
    # 2) legacy Wikidata (있으면)
    try:
        alt = get_original_name_via_wikidata(key)
    except Exception:
        alt = None
    if alt:
        return alt, {"route":"Wikidata", "note":"legacy", "key": key}
    # 3) REST fallback
    rest_val, rest_prov = get_original_name_via_wikidata_rest(key)
    return rest_val, {"route":"Wikidata(REST)", "key": key, **(rest_prov or {})}

# looks_korean_person_name 근처에 추가

_ROMAN_KOREAN_SURNAMES = {
    "kim","gim","lee","yi","ri","yoon","yun","park","pak","bak",
    "choi","choy","jeong","jung","chung","jang","chang","kang","khang",
    "han","lim","im","yim","kwon","gwon","hwang","bae","pae",
    "ryu","yu","yoo","jo","zo","oh","o","ko","go","moon","mun",
    "seo","suh","seoh","shin","sin","song","jeon","jun","cheon","chon","na","ra","ha",
}

def looks_romanized_korean_name(name: str) -> bool:
    """로마자 표기인데 한국 성으로 시작하면 한국인일 가능성이 높다고 본다."""
    s = (name or "").strip()
    if not s:
        return False
    # 한글 섞여 있으면 여기서는 패스 (이미 다른 휴리스틱이 처리)
    if _HANGUL_RE.search(s):
        return False

    # 첫 토큰만 보고, 알파벳만 남김
    first = re.split(r"[\s,]", s)[0]
    first = re.sub(r"[^A-Za-z]", "", first).lower()
    if not first:
        return False

    return first in _ROMAN_KOREAN_SURNAMES

def reorder_name_for_90010(val: str, origin_lang_code: str | None = None) -> str:
    """
    90010용 이름 재배열.
    - 700과 동일한 기본 규칙을 쓰되, LLM은 사용하지 않음.
    - origin_lang_code가 있다면 넘겨주고,
      없다면 reorder_name_by_lang 안에서 CJK 여부만 보고 처리.
    """
    s = (val or "").strip()
    if not s:
        return s

    return reorder_name_by_lang(s, origin_lang_code)


def build_90010_prefer_lod_then_wikidata_with_meta(people: dict, include_translator: bool = True):
    """
    1) NLK LOD → 2) Wikidata → 3) ko-wiki 폴백으로 원어명 생성
    - 한국 국적(P27: Q884/Q423/Q180)은 900 제외
    - QID 없으면 한글 2–4자 휴리스틱으로 한국인 추정 시 제외
    - 출력 포맷 고정: =900  10$a<원어명>  ( $9 제거 )
    - LAST_PROV_90010에 provenance trace 저장
    """
    global LAST_PROV_90010
    LAST_PROV_90010 = []

    if not people:
        return [], []

    names_author = list(people.get("author") or [])
    names_trans  = list(people.get("translator") or []) if include_translator else []
    names_all = names_author + names_trans

    out, seen, trace = [], set(), []

    for nm in names_all:
        val, prov = resolve_original_name_prefer_lod(nm)
        role = "author" if nm in names_author else "translator"

        if not val:
            trace.append({"who": nm, "resolved": None, "role": role, "provenance": prov})
            continue

        # 국적 기반 필터링 (한국인 900 제외)
        qid = None
        if isinstance(prov, dict):
            qid = prov.get("qid") or (prov.get("provenance") or {}).get("qid")
        if qid and _wd_is_korean_national(qid):
            trace.append({"who": nm, "resolved": val, "role": role,
                          "provenance": {**(prov or {}), "filtered": "korean_p27"}})
            continue
        
        # QID 없고 순수 한글 2-4자면 한국인 추정 → 제외
        if (not qid) and looks_korean_person_name(nm):
            trace.append({"who": nm, "resolved": val, "role": role,
                          "provenance": {**(prov or {}), "filtered": "korean_heuristic"}})
            continue

        # 🔥 QID 없고, 로마자 표기인데 한국 성으로 보이면 한국인으로 추정 → 제외
        if (not qid) and (looks_romanized_korean_name(nm) or looks_romanized_korean_name(val)):
            trace.append({"who": nm, "resolved": val, "role": role,
                          "provenance": {**(prov or {}), "filtered": "korean_roman_heuristic"}})
            continue


        key = (val, role)
        if key in seen:
            continue
        seen.add(key)

        val_reordered = reorder_name_for_90010(val)

        out.append(f"=900  10$a{val_reordered}")
        trace.append({
            "who": nm, "resolved": val_reordered, "role": role, "provenance": {**(prov or {}), "final": "90010"}
        })

    LAST_PROV_90010 = trace[:]
    return out, trace

def get_candidate_names_for_isbn(isbn: str) -> list[str]:
    """NLK/알라딘에서 각 1차 저자명(한글)을 뽑아 후보 리스트로 반환."""
    author_raw, _ = fetch_nlk_author_only(isbn)
    item = fetch_aladin_item(isbn)

    # NLK 첫 저자
    nlk_first = ""
    try:
        authors, _trs = split_authors_translators(author_raw or "")
        nlk_first = (authors[0] if authors else "").strip()
    except Exception:
        pass

    # 알라딘 첫 저자
    aladin_first = extract_primary_author_ko_from_aladin(item)

    out = []
    for v in [nlk_first, aladin_first]:
        if v and v not in out:
            out.append(v)
    return out

def looks_korean_person_name(name: str) -> bool:
    """한글로만 구성된 한국인 표기처럼 보이면 True"""
    s = (name or "").strip()
    if not s:
        return False
    # 라틴/키릴/가나/한자 없는 순수 한글·중점 조합이면 한국인일 확률↑
    return bool(_KOREAN_ONLY_RX.fullmatch(s))


def prewarm_wikidata_cache(all_isbns: list[str]):
    """여러 ISBN의 후보 저자명을 모아 일괄로 Wikidata 캐시를 채움."""
    all_names = []
    for isbn in all_isbns:
        all_names.extend(get_candidate_names_for_isbn(isbn))
    # 중복 제거
    seen, uniq = set(), []
    for n in all_names:
        if n and n not in seen:
            seen.add(n); uniq.append(n)

    # ✅ 한번에 배치 조회 → SQLite 캐시에 저장됨
    _ = fetch_wikidata_names_batch(uniq)







WIKIDATA_TIMEOUT = (3, 6)  # (connect, read) for requests

# 디스크 캐시 (SQLite) — 같은 이름은 재호출 금지
_cache_lock = threading.Lock()
_conn = sqlite3.connect("author_cache.sqlite3", check_same_thread=False)
_conn.execute("""CREATE TABLE IF NOT EXISTS name_cache(
  key TEXT PRIMARY KEY,
  value TEXT
)""")
_conn.commit()  # <- 한번 커밋

def cache_get(key: str):
    with _cache_lock:
        cur = _conn.execute("SELECT value FROM name_cache WHERE key=?", (key,))
        row = cur.fetchone()
    if not row:
        return None
    try:
        return json.loads(row[0])
    except Exception:
        return row[0]  # 혹시 JSON이 아니면 원문 반환

def cache_set(key: str, value: dict):
    with _cache_lock:
        _conn.execute(
            "INSERT OR REPLACE INTO name_cache(key,value) VALUES(?,?)",
            (key, json.dumps(_jsonify(value), ensure_ascii=False)),
        )
        _conn.commit()

def cache_get_sets(key: str):
    raw = cache_get(key)
    return _ensure_name_bundle(raw) if raw is not None else None
# 세트 직렬화 헬퍼는 기존(_jsonify) 그대로 사용

def cache_set_many(items: list[tuple[str, dict]]):
    """[(key, dict), ...]를 한 번에 저장 후 commit"""
    if not items:
        return
    with _cache_lock:
        _conn.executemany(
            "INSERT OR REPLACE INTO name_cache(key,value) VALUES(?,?)",
            [(k, json.dumps(_jsonify(v), ensure_ascii=False)) for k, v in items]
        )
        _conn.commit()



def _http_json(url, params=None, headers=None, timeout=(3,6)):
    try:
        r = SESSION.get(url, params=params or {}, headers=headers or {}, timeout=timeout)
        r.raise_for_status()
        return r.json()
    except Exception:
        return None

Q_JAPAN = "Q17"
Q_KOREA = "Q884"
Q_CHINA = "Q148"
Q_RUSSIA = "Q159"

def _run_sparql(q: str):
    url = "https://query.wikidata.org/sparql"
    headers = {"Accept":"application/sparql-results+json","User-Agent":"isbn2marc/1.0 (contact: local)"}
    return _http_json(url, params={"query": q, "format":"json"}, headers=headers, timeout=WIKIDATA_TIMEOUT) or {"results":{"bindings":[]}}

def fetch_wikidata_author_names_by_name(name: str) -> dict:
    """
    결과: {"native": set[str], "roman": set[str], "countries": set[str]}
    """
    import re
    name = (name or "").strip()
    if not name:
        return {"native": set(), "roman": set(), "countries": set()}

    PREFIXES = """\
PREFIX wd:  <http://www.wikidata.org/entity/>
PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX rdfs:<http://www.w3.org/2000/01/rdf-schema#>
PREFIX skos:<http://www.w3.org/2004/02/skos/core#>
"""

    query_eq = PREFIXES + """
SELECT DISTINCT ?author ?jaLabel ?zhLabel ?koLabel ?ruLabel ?enLabel ?nativeName ?country WHERE {
  ?author wdt:P31 wd:Q5 .
  ?author (rdfs:label|skos:altLabel) ?lab .
  FILTER(lang(?lab) IN ("ko","en"))
  OPTIONAL { ?author rdfs:label ?jaLabel FILTER (lang(?jaLabel) = "ja") }
  OPTIONAL { ?author rdfs:label ?zhLabel FILTER (lang(?zhLabel) = "zh") }
  OPTIONAL { ?author rdfs:label ?koLabel FILTER (lang(?koLabel) = "ko") }
  OPTIONAL { ?author rdfs:label ?ruLabel FILTER (lang(?ruLabel) = "ru") }
  OPTIONAL { ?author rdfs:label ?enLabel FILTER (lang(?enLabel) = "en") }
  OPTIONAL { ?author wdt:P1559 ?nativeName }
  OPTIONAL { ?author wdt:P27 ?country }
  FILTER(?lab = "__NAME__"@ko)
}
LIMIT 30
""".replace("__NAME__", name)

    needle = name.lower()
    query_like = PREFIXES + """
SELECT DISTINCT ?author ?jaLabel ?zhLabel ?koLabel ?ruLabel ?enLabel ?nativeName ?country WHERE {
  ?author wdt:P31 wd:Q5 .
  ?author (rdfs:label|skos:altLabel) ?lab .
  FILTER(lang(?lab) IN ("ko","en"))
  OPTIONAL { ?author rdfs:label ?jaLabel FILTER (lang(?jaLabel) = "ja") }
  OPTIONAL { ?author rdfs:label ?zhLabel FILTER (lang(?zhLabel) = "zh") }
  OPTIONAL { ?author rdfs:label ?koLabel FILTER (lang(?koLabel) = "ko") }
  OPTIONAL { ?author rdfs:label ?ruLabel FILTER (lang(?ruLabel) = "ru") }
  OPTIONAL { ?author rdfs:label ?enLabel FILTER (lang(?enLabel) = "en") }
  OPTIONAL { ?author wdt:P1559 ?nativeName }
  OPTIONAL { ?author wdt:P27 ?country }
  FILTER(CONTAINS(LCASE(?lab), "__NEEDLE__"))
}
LIMIT 30
""".replace("__NEEDLE__", needle)

    data = _run_sparql(query_eq)
    if not data.get("results", {}).get("bindings"):
        data = _run_sparql(query_like)

    native, roman, countries = set(), set(), set()
    has_cjk = lambda s: bool(re.search(r"[\u4E00-\u9FFF\u3040-\u30FF\uAC00-\uD7A3]", s))
    has_cyr = lambda s: bool(re.search(r"[\u0400-\u04FF]", s))
    has_lat = lambda s: bool(re.search(r"[A-Za-z]", s))

    for b in data.get("results", {}).get("bindings", []):
        c = b.get("country", {}).get("value", "")
        if c.startswith("http://www.wikidata.org/entity/"):
            countries.add(c.rsplit("/",1)[-1])

        ja = b.get("jaLabel", {}).get("value", "").strip()
        zh = b.get("zhLabel", {}).get("value", "").strip()
        ko = b.get("koLabel", {}).get("value", "").strip()
        ru = b.get("ruLabel", {}).get("value", "").strip()
        en = b.get("enLabel", {}).get("value", "").strip()
        nn = b.get("nativeName", {}).get("value", "").strip()

        if "Q884" in countries:   # 한국 → 정책상 90010 생략
            continue
        elif "Q17" in countries:  # 일본
            if ja: native.add(ja)
            if nn and has_cjk(nn): native.add(nn)
            if en: roman.add(en)
        elif "Q148" in countries: # 중국
            if zh: native.add(zh)
            if nn and has_cjk(nn): native.add(nn)
            if en: roman.add(en)
        elif "Q159" in countries: # 러시아
            if ru: native.add(ru)
            if nn and has_cyr(nn): native.add(nn)
            if en: roman.add(en)
        else:
            if nn:
                if has_cjk(nn): native.add(nn)
                elif has_cyr(nn): native.add(nn)
                elif has_lat(nn): roman.add(nn)
            if en: roman.add(en)

        if not (native or roman) and en:
            roman.add(en)

    return {"native": native, "roman": roman, "countries": countries}

def _ensure_name_bundle(d):
    if d is None: return {"native": set(), "roman": set(), "countries": set()}
    return {"native": set(d.get("native", [])),
            "roman": set(d.get("roman", [])),
            "countries": set(d.get("countries", []))}


def fetch_wikidata_names_batch(names: list[str]) -> dict:
    """
    여러 저자명을 batch로 Wikidata 조회 (ko 라벨 기준).
    결과: {name: {"native": set, "roman": set, "countries": set}}
    """
    import re
    if not names:
        return {}

    # 캐시 확인
    out, to_query = {}, []
    for n in names:
        cached = cache_get(f"wikidata|{n}")
        if cached:
            out[n] = _ensure_name_bundle(cached)
        else:
            to_query.append(n)

    if not to_query:
        return out

    # VALUES 블록 구성
    vals = " ".join(f'"{n}"@ko' for n in to_query)

    q = f"""
PREFIX wd:  <http://www.wikidata.org/entity/>
PREFIX wdt: <http://www.wikidata.org/prop/direct/>
PREFIX rdfs:<http://www.w3.org/2000/01/rdf-schema#>
PREFIX skos:<http://www.w3.org/2004/02/skos/core#>
SELECT DISTINCT ?name ?jaLabel ?zhLabel ?koLabel ?ruLabel ?enLabel ?nativeName ?country WHERE {{
  VALUES ?name {{ {vals} }}
  ?author wdt:P31 wd:Q5 .
  ?author (rdfs:label|skos:altLabel) ?lab .
  FILTER(?lab = ?name && lang(?lab)="ko")

  OPTIONAL {{ ?author rdfs:label ?jaLabel FILTER (lang(?jaLabel) = "ja") }}
  OPTIONAL {{ ?author rdfs:label ?zhLabel FILTER (lang(?zhLabel) = "zh") }}
  OPTIONAL {{ ?author rdfs:label ?koLabel FILTER (lang(?koLabel) = "ko") }}
  OPTIONAL {{ ?author rdfs:label ?ruLabel FILTER (lang(?ruLabel) = "ru") }}
  OPTIONAL {{ ?author rdfs:label ?enLabel FILTER (lang(?enLabel) = "en") }}
  OPTIONAL {{ ?author wdt:P1559 ?nativeName }}
  OPTIONAL {{ ?author wdt:P27 ?country }}
}} LIMIT 1000
"""

    data = _run_sparql(q)

    # grouped dict 초기화
    grouped = {n: {"native": set(), "roman": set(), "countries": set()} for n in to_query}

    for b in data.get("results", {}).get("bindings", []):
        key = b.get("name", {}).get("value", "")
        if not key:
            continue

        ja = b.get("jaLabel", {}).get("value", "").strip()
        zh = b.get("zhLabel", {}).get("value", "").strip()
        ko = b.get("koLabel", {}).get("value", "").strip()
        ru = b.get("ruLabel", {}).get("value", "").strip()
        en = b.get("enLabel", {}).get("value", "").strip()
        nn = b.get("nativeName", {}).get("value", "").strip()
        c  = b.get("country", {}).get("value", "")

        if c.startswith("http://www.wikidata.org/entity/"):
            grouped[key]["countries"].add(c.rsplit("/", 1)[-1])

        if ja: grouped[key]["native"].add(ja)
        if zh: grouped[key]["native"].add(zh)
        if ko: grouped[key]["native"].add(ko)
        if ru: grouped[key]["native"].add(ru)

        if nn:
            if re.search(r"[\u4E00-\u9FFF\u3040-\u30FF\uAC00-\uD7A3]", nn): grouped[key]["native"].add(nn)
            elif re.search(r"[\u0400-\u04FF]", nn): grouped[key]["native"].add(nn)
            elif re.search(r"[A-Za-z]", nn): grouped[key]["roman"].add(nn)

        if en:
            grouped[key]["roman"].add(en)

    # ✅ 여기 저장 파트 교체
    items = [(f"wikidata|{n}", grouped[n]) for n in to_query]
    cache_set_many(items)

    # out 병합
    for n in to_query:
        out[n] = _ensure_name_bundle(cache_get(f"wikidata|{n}"))

    return out

_CJK_RX = re.compile(r"[\u4E00-\u9FFF\u3040-\u30FF\uAC00-\uD7A3]")  # 한자/가나/한글
_CYR_RX = re.compile(r"[\u0400-\u04FF]")  # 키릴

def reorder_western_like_name(name: str) -> str:
    """
    '이름 성' → '성, 이름' 으로 바꿔주는 간단 함수.
    - 라틴/키릴 문자에만 적용
    - 한글은 그대로 반환
    """
    if not name:
        return ""
    s = name.strip()
    # CJK는 그대로
    if _CJK_RX.search(s):
        return s
    parts = s.split()
    if len(parts) >= 2:
        family = parts[-1]
        given = " ".join(parts[:-1])
        return f"{family}, {given}"
    return s


# 90010 생성기 (키릴+로마자 둘 다)

# === [REPLACE] build_90010_from_wikidata (VIAF 제거) ===

def build_90010_from_lod(people: dict, include_translator: bool = False) -> list[str]:
    """
    author(＋선택적으로 translator) 각각에 대해
    국중 LOD에서 '한글이 아닌 이름' 하나를 찾아 90010에 싣는다.
    포맷 예: =90010  \\$aФёдор Достоевский$9author
    """
    if not (people and INCLUDE_ORIGINAL_NAME_IN_90010 and USE_NLK_LOD_AUTH):
        return []

    # 대상 이름 목록
    names_author = list(people.get("author", []))
    names_trans  = list(people.get("translator", [])) if include_translator else []
    names_all = names_author + names_trans

    out, seen = [], set()
    for nm in names_all:
        orig = get_original_name_via_lod(nm)
        if not orig:
            continue
        role = "author" if nm in names_author else "translator"
        key = (orig, role)
        if key in seen:
            continue
        seen.add(key)
        out.append(f"=90010  \\\\$a{orig}$9{role}")
    return out





# =========================
# 🧹 문자열/245 유틸
# =========================
DELIMS = [": ", " : ", ":", " - ", " — ", "–", "—", "-", " · ", "·", "; ", ";", " | ", "|", "/"]

def _compat_normalize(s: str) -> str:
    if not s:
        return ""
    s = s.replace("：", ":").replace("－", "-").replace("‧", "·").replace("／", "/")
    s = re.sub(r"[\u2000-\u200f\u202a-\u202e]", "", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s

_TRAIL_PAREN_PAT = re.compile(
    r"""\s*(?:[\(\[](
        개정|증보|개역|전정|합본|전면개정|개정판|증보판|신판|보급판|
        최신개정판|개정증보판|국역|번역|영문판|초판|제?\d+\s*판|
        \d+\s*주년\s*기념판|기념판|
        [^()\[\]]*총서[^()\[\]]*|[^()\[\]]*시리즈[^()\[\]]*
    )[\)\]])\s*$""",
    re.IGNORECASE | re.VERBOSE
)

def _strip_trailing_paren_notes(s: str) -> str:
    return _TRAIL_PAREN_PAT.sub("", s).strip(" .,/;:-—·|")

def _clean_piece(s: str) -> str:
    if not s:
        return ""
    s = _compat_normalize(s)
    s = _strip_trailing_paren_notes(s)
    s = s.strip(" .,/;:-—·|")
    return s

def _find_top_level_split(text: str, delims=DELIMS):
    pairs = {"(": ")", "[": "]", "{": "}", "〈": "〉", "《": "》", "「": "」", "『": "』", "“": "”", "‘": "’", "«": "»"}
    opens, closes = set(pairs), {v: k for k, v in pairs.items()}
    stack, i, L = [], 0, len(text)
    while i < L:
        ch = text[i]
        if ch in opens:
            stack.append(ch); i += 1; continue
        if ch in closes:
            if stack and pairs.get(stack[-1]) == ch: stack.pop()
            i += 1; continue
        if not stack:
            for d in delims:
                if text.startswith(d, i):
                    return i, d
        i += 1
    return None

def split_title_only_for_245(title: str):
    if not title:
        return "", None
    t = _compat_normalize(title)
    hit = _find_top_level_split(t, DELIMS)
    if not hit:
        return _clean_piece(t), None
    idx, delim = hit
    left, right = t[:idx], t[idx + len(delim):]
    return _clean_piece(left), (_clean_piece(right) or None)

def extract_245_from_aladin_item(item: dict, collapse_a_spaces: bool = True):
    raw_title = (item.get("title") or "")
    raw_sub   = (item.get("subInfo", {}) or {}).get("subTitle") or ""

    # 1) 알라딘의 title/subTitle에서 기본 $a/$b 추출 (네 기존 로직)
    t = _compat_normalize(raw_title)
    s = _clean_piece(raw_sub)
    if s:
        tail = [f" : {s}", f": {s}", f":{s}", f" - {s}", f"- {s}", f"-{s}"]
        t_removed = t
        for pat in tail:
            if t_removed.endswith(pat):
                t_removed = t_removed[: -len(pat)]
                break
        a0, b = _clean_piece(t_removed) or _clean_piece(t), s
    else:
        a0, b = split_title_only_for_245(t)

    # 2) $a 끝의 권차 후보를 $n으로 떼기 > 일단 주석처리!! 디테일 잡기가 어려움 ㅠ
    # a_base, n = _split_part_suffix_for_245(a0, item)
    a_base = a0
    n = ""

    # 3) $a 공백 유지/제거 옵션
    a_out = a_base.replace(" ", "") if collapse_a_spaces else a_base

    # 4) MRK 조립 ($n은 $a 다음, $b보다 먼저)
    line = f"=245  00$a{a_out}"
    if n:
        line += (" " if a_out.endswith(".") else " .")  # a_out이 이미 '.'로 끝나면 공백만, 아니면 ' .' 추가
        line += f"$n{n}"
    if b:
        line += f" :$b{b}"

    return {"ind1":"0","ind2":"0","a":a_out,"b":b,"n":n,"mrk":line}


# 권차 후보 판단에 쓰는 키워드/패턴
_PART_LABEL_RX = re.compile(
    r"(?:제?\s*\d+\s*(?:권|부|편|책)|"     # 제1권/1권/1부/1편/1책
    r"[IVXLCDM]+|"                         # 로마 숫자 I, II, III ...
    r"[상중하]|[전후])$",                  # 상/중/하, 전/후
    re.IGNORECASE
)

def _has_series_evidence(item: dict) -> bool:
    """시리즈/원제 등 권차 가능성 보강 신호"""
    series = item.get("seriesInfo") or {}
    sub    = item.get("subInfo") or {}
    # seriesName/ID가 있으면 시리즈 가능성↑
    if series.get("seriesName") or series.get("seriesId"):
        return True
    # 원제가 있고, 원제는 숫자로 끝나지 않는데 한글제목만 숫자로 끝나면 권차 가능성↑
    orig = (sub.get("originalTitle") or "").strip()
    if orig and not re.search(r"\d\s*$", orig):
        return True
    return False

def _split_part_suffix_for_245(a_raw: str, item: dict) -> tuple[str, str|None]:
    """
    제목 $a 후보 문자열에서 끝의 권차/부/편/숫자/로마숫자/상중하/전후 등을 떼어 $n으로.
    반환: (a_base, n_or_None)
    """
    if not a_raw:
        return "", None

    a = _clean_piece(a_raw)  # 네가 이미 쓰고 있는 정리 함수
    # (1) 전부 숫자/로마숫자인 제목은 '숫자 제목'으로 보고 분리하지 않음 (예: '1984')
    if re.fullmatch(r"\d+|[IVXLCDM]+", a, re.IGNORECASE):
        return a, None

    # (2) '... (제1권)' 같은 괄호형 권차 → 우선 처리
    m_paren = re.search(r"\s*[\(\[]\s*([^()\[\]]+)\s*[\)\]]\s*$", a)
    if m_paren and _PART_LABEL_RX.search(m_paren.group(1).strip()):
        n_token = m_paren.group(1).strip()
        a_base  = a[: m_paren.start()].rstrip(" .,/;:-—·|")
        # '제1권'은 숫자만 남겨 주는 게 깔끔
        m_num = re.search(r"\d+", n_token)
        return a_base, (m_num.group(0) if m_num else n_token)

    # (3) 라벨형 권차(붙은 형태 포함): '... 제1권' / '... 1권' / '... 1부' / '...1편'
    m_label = re.search(r"\s*(제?\s*\d+\s*(?:권|부|편|책))\s*$", a, re.IGNORECASE)
    if m_label:
        a_base = a[: m_label.start()].rstrip(" .,/;:-—·|")
        num    = re.search(r"\d+", m_label.group(1))
        return a_base, (num.group(0) if num else m_label.group(1).strip())

    # (4) 상/중/하, 전/후
    m_kor = re.search(r"\s*([상중하]|[전후])\s*$", a)
    if m_kor:
        a_base = a[: m_kor.start()].rstrip(" .,/;:-—·|")
        return a_base, m_kor.group(1)

    # (5) 로마숫자 (I, II, III, …)
    m_roman = re.search(r"\s*([IVXLCDM]+)\s*$", a, re.IGNORECASE)
    if m_roman:
        a_base = a[: m_roman.start()].rstrip(" .,/;:-—·|")
        token  = m_roman.group(1)
        # a 전체가 로마숫자만은 아닌지 위에서 한 번 더 체크했으니 OK
        return a_base, token

    # (6) 맨 끝 '맨바로 숫자' — 과대 분리 방지 위해 '시리즈/원제' 같은 보강 신호가 있을 때만
    m_tailnum = re.search(r"\s*(\d{1,3})\s*$", a)
    if m_tailnum and _has_series_evidence(item):
        a_base = a[: m_tailnum.start()].rstrip(" .,/;:-—·|")
        # '파이썬 3' 같은 '판/개정'은 뒤에 '판/쇄/ed'가 붙는 경우가 많아 여기엔 안 걸림
        if a_base:  # 베이스가 비지 않을 때만 (전부 숫자인 제목 방지)
            return a_base, m_tailnum.group(1)

    # (7) 분리 못 하면 그대로
    return a, None

def get_title_a_from_aladin(item: dict) -> str:
    # 245 $a로 쓰는 본표제만 (부제 제외) — 245 빌더와 동일 정리 규칙
    import re
    t = ((item or {}).get("title") or "").strip()
    t = re.sub(r"\s+([:;,./])", r"\1", t).strip()
    t = re.sub(r"[.:;,/]\s*$", "", t).strip()
    return t

def parse_245_a_n(marc245_line: str) -> tuple[str, str | None]:
    """
    '=245  00$a...$n...$b...' 한 줄에서
    - $a(본표제)만
    - $n(권차표시) 유무/값
    을 뽑아준다.
    """
    if not marc245_line:
        return "", None

    # $a 추출
    m_a = re.search(r"=245\s+\d{2}\$a(.*?)(?=\$[a-z]|$)", marc245_line)
    a_out = (m_a.group(1).strip() if m_a else "").strip()

    # $a 끝의 불필요한 구두점 정리 (.,:;/ 공백)
    a_out = re.sub(r"\s+([:;,./])", r"\1", a_out)
    a_out = re.sub(r"[.:;,/]\s*$", "", a_out).strip()

    # $n 추출 (있으면 숫자 읽기 금지에 쓰임)
    m_n = re.search(r"\$n(.*?)(?=\$[a-z]|$)", marc245_line)
    n_val = m_n.group(1).strip() if m_n else None

    return a_out, n_val if n_val else None

# """알라딘 originalTitle이 있으면 246 19 $a 로 반환"""

# 원제 끝의 (YYYY/YYY년), (rev. ed.), (2nd ed.), (제2판) 등 제거
_YEAR_OR_EDITION_PAREN_PAT = re.compile(
    r"""
    \s*
    \(
      \s*
      (?:                                # 아래 중 하나라도 맞으면 삭제
         \d{3,4}\s*년?                   # 1866, 1866년, 1942 등
        |rev(?:ised)?\.?\s*ed\.?         # rev. ed., revised ed.
        |(?:\d+(?:st|nd|rd|th)\s*ed\.?)  # 2nd ed., 3rd ed.
        |edition                         # edition
        |ed\.?                           # ed.
        |제?\s*\d+\s*판                   # 제2판, 2판
        |개정(?:증보)?판?                 # 개정판, 개정증보판
        |증보판|초판|신판|보급판
      )
      [^()\[\]]*
    \)
    \s*$
    """,
    re.IGNORECASE | re.VERBOSE
)


def build_246_from_aladin_item(item: dict) -> str | None:
    if not item:
        return None
    orig = ((item.get("subInfo") or {}).get("originalTitle") or "").strip()
    # 1) 우리 공통 클린업: 앞뒤 공백/기호, 괄호형 판·시리즈 꼬리 제거
    orig = _clean_piece(orig)  # _strip_trailing_paren_notes 포함:contentReference[oaicite:2]{index=2}

    # 2) 끝의 (YYYY/년)·영문판 표기 등 추가 제거
    orig = _YEAR_OR_EDITION_PAREN_PAT.sub("", orig).strip()

    if orig:
        return f"=246  19$a{orig}"
    return None



# =========================
# 🔎 외부 API (NLK / 알라딘)
# =========================
from urllib.parse import urlencode

def build_nlk_url_json(isbn: str, page_no: int = 1, page_size: int = 1) -> str:
    base = "https://seoji.nl.go.kr/landingPage/SearchApi.do"
    qs = urlencode({
        "cert_key": NLK_CERT_KEY,
        "result_style": "json",
        "page_no": page_no,
        "page_size": page_size,
        "isbn": isbn
    })
    return f"{base}?{qs}"

def fetch_nlk_seoji_json(isbn: str):
    """다중 엔드포인트 순차 시도 → (첫 성공) (레코드, 실제 URL) 반환"""
    if not NLK_CERT_KEY:
        raise RuntimeError("NLK_CERT_KEY 미설정")

    attempts = [
        "https://seoji.nl.go.kr/landingPage/SearchApi.do",
        "https://www.nl.go.kr/seoji/SearchApi.do",
        "http://seoji.nl.go.kr/landingPage/SearchApi.do",
        "http://www.nl.go.kr/seoji/SearchApi.do",
    ]
    params = {
        "cert_key": NLK_CERT_KEY, "result_style": "json",
        "page_no": 1, "page_size": 1, "isbn": isbn
    }
    last_err = None
    for base in attempts:
        try:
            r = SESSION.get(base, params=params, timeout=(10, 30))
            r.raise_for_status()
            data = r.json()
            docs = data.get("docs") or data.get("DOCS") or []
            if docs:
                return docs[0], r.url
        except Exception as e:
            last_err = e
            continue
    raise RuntimeError(f"NLK JSON 실패: {last_err}")

def fetch_nlk_author_only(isbn: str):
    """(AUTHOR 원문, 실제 사용 URL)"""
    try:
        rec, used_url = fetch_nlk_seoji_json(isbn)
        author = get_anycase(rec, "AUTHOR") or ""
        return author, used_url
    except Exception:
        return "", build_nlk_url_json(isbn)

def fetch_aladin_item(isbn13: str) -> dict:
    if not ALADIN_TTB_KEY:
        raise RuntimeError("ALADIN_TTB_KEY 미설정")
    url = "http://www.aladin.co.kr/ttb/api/ItemLookUp.aspx"
    params = {
        "ttbkey": ALADIN_TTB_KEY, "itemIdType": "ISBN13",
        "ItemId": isbn13, "output": "js", "Version": "20131101",
    }
    r = SESSION.get(url, params=params, timeout=(5, 20))
    r.raise_for_status()
    data = r.json()
    return (data.get("item") or [{}])[0]


# === 940: AI 보강 ===


_ai940_lock = threading.Lock()
_ai940_conn = sqlite3.connect("author_cache.sqlite3", check_same_thread=False)
_ai940_conn.execute("""CREATE TABLE IF NOT EXISTS name_cache(
  key TEXT PRIMARY KEY,
  value TEXT
)""")

def _ai940_get(key: str):
    with _ai940_lock:
        cur = _ai940_conn.execute("SELECT value FROM name_cache WHERE key=?", (key,))
        row = cur.fetchone()
    return json.loads(row[0]) if row else None

def _ai940_set(key: str, value: list[str]):
    with _ai940_lock:
        _ai940_conn.execute("INSERT OR REPLACE INTO name_cache(key,value) VALUES(?,?)",
                            (key, json.dumps(value, ensure_ascii=False)))
        _ai940_conn.commit()

def ai_korean_readings(title: str, n: int = 4) -> List[str]:
    title = (title or "").strip()
    if not title or _client is None:
        return []

    key = f"ai940|{title}"
    cached = _ai940_get(key)
    if cached is not None:
        return cached[:n]

    try:
        sys = (
            "역할: 한국어 도서 서명 '발음 표기 생성기'. "
            "입력 서명의 영어/숫자를 자연스러운 한국어 발음으로 바꾸어라. "
            "각 줄에 하나의 변형만 출력. 설명/번호/기호 금지. 최대 6줄."
        )
        prompt = (
            f"서명: {title}\n"
            "지침: 표기는 한국어로만, 맞춤법 준수. "
            "예: 2025→이천이십오, 2.0→이점영, ChatGPT→챗지피티"
        )
        resp = _client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role":"system","content":sys},
                      {"role":"user","content":prompt}],
            temperature=0.3,
        )
        text = (resp.choices[0].message.content or "").strip()
        lines = [re.sub(r"^\d+[\).\s-]*", "", x).strip() for x in text.splitlines() if x.strip()]
        lines = [l for l in lines if l and l != title and re.search(r"[가-힣]", l)]
        _ai940_set(key, lines)
        return lines[:n]
    except Exception:
        return []



EN_KO_MAP = {
    "chatgpt": "챗지피티",
    "gpt": "지피티",
    "ai": "에이아이",
    "api": "에이피아이",
    "ml": "엠엘",
    "nlp": "엔엘피",
    "llm": "엘엘엠",
    "excel": "엑셀",
    "youtube": "유튜브",
}

# 소수 등 특정 패턴 고정 읽기
DECIMAL_MAP = {
    "2.0": "이점영",   # ← 요청 반영!
    "3.0": "삼점영",
    "4.0": "사점영",
}

SINO = {"0":"영","1":"일","2":"이","3":"삼","4":"사","5":"오","6":"육","7":"칠","8":"팔","9":"구"}
ZERO_ALT = ["영", "공"]  # 자릿수 읽기 대안

def replace_decimals(text: str) -> str:
    for k, v in DECIMAL_MAP.items():
        text = text.replace(k, v)
    return text

def replace_english_simple(text: str) -> str:
    if not EN_KO_MAP: 
        return text
    def _sub(m):
        return EN_KO_MAP.get(m.group(0).lower(), m.group(0))
    pattern = r"\b(" + "|".join(map(re.escape, EN_KO_MAP.keys())) + r")\b"
    return re.sub(pattern, _sub, text, flags=re.IGNORECASE)

def _read_year_yyyy(num: str) -> str:
    n = int(num)
    th = n // 1000; hu = (n // 100) % 10; te = (n // 10) % 10; on = n % 10
    out = []
    if th: out.append(SINO[str(th)] + "천")
    if hu: out.append(SINO[str(hu)] + "백")
    if te: out.append("십" if te==1 else SINO[str(te)] + "십")
    if on: out.append(SINO[str(on)])
    return "".join(out) if out else "영"

def _read_cardinal(num: str) -> str:
    return _read_year_yyyy(num)

def _read_digits(num: str, zero="영") -> str:
    return "".join(SINO[ch] if ch in SINO and ch != "0" else (zero if ch=="0" else ch) for ch in num)

def generate_korean_title_variants(title: str, max_variants: int = 5) -> List[str]:
    """
    규칙 기반 변형 생성:
      - 영문 간이 치환
      - 소수 고정 치환 (예: 2.0→이점영)
      - 숫자: 연도식/자릿수(영·공) 읽기
    """
    base0 = (title or "").strip()
    base = replace_decimals(base0)
    base = replace_english_simple(base)

    variants = {base0, base}

    nums = re.findall(r"\d{2,}", base0)
    if nums:
        # 각 숫자에 대해 대표 읽기 후보 생성
        per_num_choices = []
        for n in nums:
            local = {_read_cardinal(n)}
            if len(n) == 4 and 1000 <= int(n) <= 2999:
                local.add(_read_year_yyyy(n))
            for z in ZERO_ALT:
                local.add(_read_digits(n, zero=z))
            per_num_choices.append(sorted(local, key=len))

        # 순차 적용으로 조합 폭발 방지
        work = {base}
        for i, choices in enumerate(per_num_choices):
            new_work = set()
            for w in work:
                # 해당 차례의 숫자만 1회 치환
                cnt = 0
                for c in choices:
                    def _repl(m, idx=i, repl=c):
                        nonlocal cnt
                        if cnt==0 and m.group(0)==nums[idx]:
                            cnt = 1
                            return repl
                        return m.group(0)
                    new_work.add(re.sub(r"\d{2,}", _repl, w))
            work = new_work
        variants |= work

    # 후처리
    outs = []
    for v in variants:
        if not v: continue
        v = re.sub(r"\s+([:;,./])", r"\1", v).strip()
        outs.append(v)
    outs = sorted(set(outs), key=lambda s: (len(s), s))
    return outs[:max_variants]

def build_940_from_title_a(title_a: str, use_ai: bool = True, *, disable_number_reading: bool = False) -> list[str]:
    import re
    base = (title_a or "").strip()
    if not base:
        return []

    # 숫자/영문 없으면 생성 생략
    if not re.search(r"[0-9A-Za-z]", base):
        return []

    # 규칙 기반
    if disable_number_reading:
        # 숫자 읽기를 막고, 영어 치환/소수 고정만 적용
        v0 = replace_english_simple(base) if 'replace_english_simple' in globals() else base
        variants = sorted({v0})
    else:
        variants = generate_korean_title_variants(base, max_variants=5)

    # AI 보강(엄격 모드)
    if 'ai_korean_readings_strict' in globals():
        variants += ai_korean_readings_strict(base, n=4)
    else:
        variants += ai_korean_readings(base, n=4)

    def _illegal_punct(v: str) -> bool:
        new_colon = (":" in v) and (":" not in base)
        new_dash  = (" - " in v) and (" - " not in base) and ("-" not in base)
        return new_colon or new_dash

    out, seen = [], set()
    for v in variants:
        v = (v or "").strip()
        if not v or v == base: 
            continue
        if _illegal_punct(v):
            continue
        if v not in seen:
            seen.add(v)
            out.append(f"=940  \\\\$a{v}")
    return out[:6]

def ai_korean_readings_strict(title_a: str, n: int = 4) -> list[str]:
    """
    OpenAI로 숫자/영문을 한국어 발음으로 변환 (입력 $a만 사용)
    - 부제/추가 단어/콜론/대시 추가 금지
    """
    import re
    if not title_a or _client is None:
        return []

    key = f"ai940|strict|{title_a}"
    cached = _ai940_get(key)
    if cached is not None:
        return cached[:n]

    try:
        sys = (
            "역할: 한국어 도서 서명 '발음 표기 생성기'. "
            "주어진 본표제(245 $a)에서 숫자/영문만 한국어 발음으로 치환하라. "
            "입력에 없는 단어/부제($b) 추가 금지. 콜론(:), 대시(-) 등 새 구두점 추가 금지. "
            "각 줄에 1개 변형만, 순수 텍스트만 출력."
        )
        prompt = (
            f"본표제(245 $a): {title_a}\n"
            "예: 2025→이천이십오, 2.0→이점영, ChatGPT→챗지피티"
        )
        resp = _client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role":"system","content":sys},
                      {"role":"user","content":prompt}],
            temperature=0.2,
        )
        text = (resp.choices[0].message.content or "").strip()
        lines = [re.sub(r"^\d+[\).\s-]*", "", x).strip() for x in text.splitlines() if x.strip()]
        # 한글 포함 + base 미포함 구두점 금지
        safe = []
        for l in lines:
            if not re.search(r"[가-힣]", l):
                continue
            # 입력에 없던 콜론/대시 추가 금지
            if (":" in l and ":" not in title_a) or (" - " in l and " - " not in title_a and "-" not in title_a):
                continue
            safe.append(l)
        _ai940_set(key, safe)
        return safe[:n]
    except Exception:
        return []



def build_049(reg_mark: str, reg_no: str, copy_symbol: str) -> str:
    """
    049 소장사항 필드 생성
    - $I 등록기호+등록번호
    - $f 별치기호 (있을 때만)
    """
    reg_mark = (reg_mark or "").strip()
    reg_no = (reg_no or "").strip()
    copy_symbol = (copy_symbol or "").strip()

    if not (reg_mark or reg_no):
        field = "=049  0\\$lEMQ999999"  # 등록기호+등록번호 없으면 생성 안 함 > EMQ999999 출력
        if copy_symbol:
            field += f"$f{copy_symbol}"
        return field

    field = f"=049  0\\$l{reg_mark}{reg_no}"
    if copy_symbol:
        field += f"$f{copy_symbol}"
    return field

# =========================
# 👤 NLK AUTHOR → 저자/역자 분리 & 700
# =========================

def _extract_lang_h_from_041(tag_041_text: str | None) -> str | None:
    if not tag_041_text:
        return None
    m = re.search(r"\$h([a-z]{3})", tag_041_text, re.IGNORECASE)
    return m.group(1).lower() if m else None

# 사람 단위 분할(세미콜론은 그룹 분리로 다룸)
SEP_PATTERN = re.compile(r"\s*[,/&·]\s*|\s+and\s+|\s+with\s+|\s*\|\s*", re.IGNORECASE)

# 저자 라벨(‘그림/삽화/일러스트/그린’ 포함, ‘글·그림’도 저자)
ROLE_AUTHOR_LABELS = (
    r"(?:지은이|저자|저|저술|집필|원작|원저|"
    r"글|글쓴이|글작가|스토리|각색|만화|"
    r"그림|그림작가|삽화|일러스트(?:레이터)?|그린|"
    r"글\s*[\u00B7·/,\+]\s*그림|그림\s*[\u00B7·/,\+]\s*글|글\s*그림|글그림)"
)
# 역자 라벨(축약 ‘역’ 포함)
ROLE_TRANS_LABELS = r"(?:옮긴이|옮김|역자|역|번역자?|역해|역주|공역)"

# 말미 역할(‘이름 역할’)
ROLE_AUTHOR_TRAIL = (
    r"(?:글|지음|지은이|저자|저|저술|집필|원작|원저|"
    r"그림|그림작가|삽화|일러스트(?:레이터)?|그린|스토리|각색|만화|채색)"
)
ROLE_TRANS_TRAIL = r"(?:옮김|번역|번역자|역자|역|역해|역주|공역)"

def _strip_trailing_role(piece: str) -> str:
    return re.sub(
        rf"\s+(?:{ROLE_AUTHOR_TRAIL}|{ROLE_TRANS_TRAIL})\s*[\)\].,;:]*$",
        "", piece, flags=re.IGNORECASE
    ).strip()

def split_authors_translators(nlk_author_raw: str):
    """AUTHOR 문자열을 저자/역자 리스트로 분리"""
    if not nlk_author_raw:
        return [], []
    s = re.sub(r"\s+", " ", nlk_author_raw.strip())
    # 괄호형 역할 → 말미 노출
    s = re.sub(
        rf"\(\s*({ROLE_AUTHOR_LABELS}|{ROLE_TRANS_LABELS})\s*\)",
        lambda m: " " + m.group(1), s, flags=re.IGNORECASE
    )
    authors, translators = [], []
    groups = [g.strip() for g in re.split(r"\s*;\s*", s) if g.strip()]
    for g in groups:
        # 레이블형
        m_lab = re.match(
            rf"(?P<label>{ROLE_AUTHOR_LABELS}|{ROLE_TRANS_LABELS})\s*:\s*(?P<names>.+)$",
            g, flags=re.IGNORECASE
        )
        if m_lab:
            label = m_lab.group("label"); names_part = m_lab.group("names")
            parts = [p.strip() for p in SEP_PATTERN.split(names_part) if p.strip()]
            (authors if re.match(ROLE_AUTHOR_LABELS, label, re.IGNORECASE) else translators).extend(parts)
            continue
        # 말미형/무표시
        chunks = [p.strip() for p in SEP_PATTERN.split(g) if p.strip()]
        for ch in chunks:
            is_author = bool(re.search(rf"\s+{ROLE_AUTHOR_TRAIL}$", ch, re.IGNORECASE) or
                             re.search(ROLE_AUTHOR_LABELS, ch, re.IGNORECASE))
            is_trans  = bool(re.search(rf"\s+{ROLE_TRANS_TRAIL}$", ch, re.IGNORECASE) or
                             re.search(ROLE_TRANS_LABELS, ch, re.IGNORECASE))
            base = _strip_trailing_role(ch)
            if is_author and not is_trans:
                authors.append(base)
            elif is_trans and not is_author:
                translators.append(base)
            else:
                authors.append(base)  # 무표시는 기본 저자
    # 순서 유지 중복 제거
    seen = set(); authors = [x for x in authors if not (x in seen or seen.add(x))]
    seen = set(); translators = [x for x in translators if not (x in seen or seen.add(x))]
    return authors, translators

def parse_nlk_authors(nlk_author_raw: str):
    """역할어 제거 후, 사람 이름만(저자/역자 합쳐서) 리스트로 추출 → 700 생성용"""
    if not nlk_author_raw:
        return []
    s = nlk_author_raw
    ROLE_ANY_LABELS = rf"(?:{ROLE_AUTHOR_LABELS}|{ROLE_TRANS_LABELS})"
    ROLE_ANY_TRAIL  = rf"(?:{ROLE_AUTHOR_TRAIL}|{ROLE_TRANS_TRAIL})"
    # 레이블형/괄호형/말미형 역할어 제거
    s = re.sub(rf"{ROLE_ANY_LABELS}\s*:\s*", "", s, flags=re.IGNORECASE)
    s = re.sub(rf"\(\s*{ROLE_ANY_LABELS}\s*\)", "", s, flags=re.IGNORECASE)
    s = re.sub(rf"\s+{ROLE_ANY_TRAIL}(?=$|[\s),.;/|])", "", s, flags=re.IGNORECASE)
    # 사람 단위 분리
    chunks = [c for c in SEP_PATTERN.split(s) if c and c.strip()]
    return [re.sub(r"\s+", " ", c).strip() for c in chunks]

def build_700_from_nlk_author(nlk_author_raw: str, *, aladin_item: dict | None = None):
    authors, translators = split_authors_translators(nlk_author_raw)
    names = authors + translators  # 저자들 → 역자들 순서
    lines = []
    for nm in names:
        if not nm.strip():
            continue
        fixed = reorder_hangul_name_for_700(nm, aladin_item=item, origin_lang_code=origin_lang)
        lines.append(f"=700  1\\$a{fixed}")
    return lines

# ===============================
# 245 필드 구성 (제목 / 책임표시)
# ===============================
def build_245_with_people_from_sources(aladin_item: dict, nlk_author_raw: str, prefer="aladin") -> str:
    tb = extract_245_from_aladin_item(aladin_item, collapse_a_spaces=False)
    a_out, b, n = tb["a"], tb.get("b"), tb.get("n")

    line = f"=245  00$a{a_out}"
    if n:
        line += (" " if a_out.endswith(".") else " .") + f"$n{n}"
    if b:
        line += f" :$b{b}"

    # --- 인물 데이터 가져오기 ---
    people = extract_people_from_aladin(aladin_item) if (prefer == "aladin" and aladin_item) else None
    authors = (people or {}).get("author", [])
    edtrs   = (people or {}).get("editor", [])
    illus   = (people or {}).get("illustrator", [])
    trans   = (people or {}).get("translator", [])

    if not (authors or trans or illus or edtrs):
        parsed = parse_people_flexible(nlk_author_raw or "")
        authors = parsed.get("author", [])
        edtrs   = parsed.get("editor", [])
        illus   = parsed.get("illustrator", [])
        trans   = parsed.get("translator", [])

    # --- 이름 정리 ---
    def clean_name_list(names, remove_words):
        result = []
        for name in names:
            clean = name
            for w in remove_words:
                clean = clean.replace(w, "")
            result.append(clean.strip())
        return result

    authors = clean_name_list(authors, ["(지은이)", "(저자)"])
    edtrs   = clean_name_list(edtrs, ["(엮은이)", "(편집)", "(편저)"])
    illus   = clean_name_list(illus, ["(그림)", "(그린이)", "(일러스트)", "(삽화)"])
    trans   = clean_name_list(trans, ["(옮긴이)", "(역자)", "(번역)"])

    # --- 파트 조립 ---
    parts = []

    # 1️⃣ 지은이
    if authors:
        seg = []
        head, tail = authors[0], authors[1:]
        seg.append(f"$d{head}")
        for t in tail:
            seg.append(f"$e{t}")
        parts.append(", ".join(seg) + " 지음")

    # 2️⃣ 엮은이
    if edtrs:
        seg = []
        head, tail = edtrs[0], edtrs[1:]
        seg.append(f"$e{head}")
        for t in tail:
            seg.append(f"$e{t}")
        parts.append(", ".join(seg) + " 엮음")

    # 3️⃣ 그림 (illustrator)
    if illus:
        seg = []
        head, tail = illus[0], illus[1:]
        seg.append(f"$e{head}")
        for t in tail:
            seg.append(f"$e{t}")
        parts.append(", ".join(seg) + " 그림")

    # 4️⃣ 옮긴이
    if trans:
        seg = []
        head, tail = trans[0], trans[1:]
        seg.append(f"$e{head}")
        for t in tail:
            seg.append(f"$e{t}")
        parts.append(", ".join(seg) + " 옮김")

    # --- 합치기 ---
    if parts:
        line += " /" + " ; ".join(parts)

    return line

def build_700_people_pref_aladin(
    author_raw: str,
    aladin_item: dict,
    origin_lang_code: str | None = None
):
    people = extract_people_from_aladin(aladin_item) if aladin_item else {}

    def _reorder(name, aladin_item=None):
        return reorder_hangul_name_for_700(
            name,
            aladin_item=aladin_item,
            origin_lang_code=origin_lang_code
        )

    if people.get("author") or people.get("translator"):
        return build_700_from_people(
            people,
            reorder_fn=_reorder,
            aladin_item=aladin_item
        )

    if author_raw:
        parsed = parse_people_flexible(author_raw)
        return build_700_from_people(
            parsed,
            reorder_fn=_reorder,
            aladin_item=aladin_item
        )

    return []


# 이름 뒤에 역할 꼬리표 제거용
_ROLE_SUFFIX_RX = re.compile(r"\s*(지음|지은이|엮음|옮김|역|편|글|그림)\s*$")

def _strip_role_suffix(s: str) -> str:
    return _ROLE_SUFFIX_RX.sub("", (s or "").strip())

def extract_primary_author_ko_from_aladin(item: dict) -> str:
    """
    알라딘 item에서 '첫 저자(지은이)' 한글 표기를 추출한다.
    예) "도스토옙스키 (지은이), 이정식 (옮긴이)" → "도스토옙스키"
    우선순위: subInfo.authors 배열(지은이/저자) → 전체 author 문자열 파싱
    """
    if not item:
        return ""

    sub = (item.get("subInfo") or {})

    # 1) 구조화된 authors 배열 우선
    authors_list = sub.get("authors")
    if isinstance(authors_list, list) and authors_list:
        # (1) authorTypeName에 '지은이' 또는 '저자' 포함 찾기
        for a in authors_list:
            atype = (a.get("authorTypeName") or a.get("authorType") or "").strip()
            nm = (a.get("authorName") or a.get("name") or "").strip()
            if not nm:
                continue
            if ("지은이" in atype) or ("저자" in atype):
                return _strip_role_suffix(nm)
        # (2) 못 찾으면 첫 항목의 이름
        first = (authors_list[0].get("authorName") or authors_list[0].get("name") or "").strip()
        return _strip_role_suffix(first)

    # 2) 문자열 필드 파싱 (예: "도스토옙스키 (지은이), 이정식 (옮긴이)")
    author_str = (item.get("author") or "").strip()
    if author_str:
        first_seg = author_str.split(",")[0]
        # 끝의 "(역자)" "(지은이)" 등 괄호 역할 제거
        first = re.sub(r"\s*\(.*?\)\s*$", "", first_seg).strip()
        # 역할 꼬리표(지음/옮김 등) 제거
        first = _strip_role_suffix(first)
        return first

    return ""



# --- 700 동아시아 보정에 필요한 전역/헬퍼  ---
# 900 생성 때 쌓는 provenance가 비어 있어도 안전하게 기본값 보장
try:
    LAST_PROV_90010
except NameError:
    LAST_PROV_90010 = []

# 동아시아 국가(QID) 세트
_EAST_ASIAN_P27 = {"Q17","Q148","Q884","Q423","Q865","Q864","Q14773"}

def _east_asian_konames_from_prov(prov900: list[dict]) -> set[str]:
    """
    900 provenance에서 동아시아 국적(P27)이 확인된 인물의 한글표기('who') 집합을 만든다.
    P27 조회 함수(_wd_get_p27_list)가 없거나 실패하면 조용히 건너뜀(안전).
    """
    out = set()
    if not prov900:
        return out
    for t in prov900:
        try:
            prov = t.get("provenance") if isinstance(t, dict) else None
            qid = None
            if isinstance(prov, dict):
                qid = prov.get("qid") or (prov.get("provenance") or {}).get("qid")
            who = (t.get("who") or "").strip()
            if not (qid and who):
                continue
            # 국적(P27) 체크 (함수 존재 시)
            is_east = False
            try:
                p27s = _wd_get_p27_list(qid)  # 없으면 except로 넘어감
                if p27s and any(c in _EAST_ASIAN_P27 for c in p27s):
                    is_east = True
            except Exception:
                # P27 조회 불가 시엔 보수적으로 '동아시아 아님' 처리
                is_east = False
            if is_east:
                out.add(who)
        except Exception:
            # provenance 형식이 예상과 달라도 전체 실패하지 않도록 무시
            pass
    return out

def _fix_700_order_with_nationality(lines: list[str], east_konames: set[str]) -> list[str]:
    """
    700 라인에서 '이름, 성' 형태가 있을 때,
    (who 기준) 동아시아 인물은 '성 이름'(쉼표 없음)으로 보정한다.
    """
    if not lines or not east_konames:
        return lines or []

    import re
    patt = re.compile(r"^(=700\s\s1\\?\$a)([^,]+),\s*([^$\r\n]+)(.*)$")
    out = []
    for ln in lines:
        m = patt.match(ln)
        if not m:
            out.append(ln)
            continue
        prefix, left, right, suffix = m.groups()  # left=이름, right=성 (한글)
        candidate = f"{right.strip()} {left.strip()}"  # '성 이름'
        if candidate in east_konames:
            out.append(f"{prefix}{candidate}{suffix}")
        else:
            out.append(ln)
    return out


# ============================= 한국 발행지 문자열 → KORMARC 3자리 코드 (필요 시 확장)
KR_REGION_TO_CODE = {
    "서울": "ulk", "서울특별시": "ulk",
    "경기": "ggk", "경기도": "ggk",
    "부산": "bnk", "부산광역시": "bnk",
    "대구": "tgk", "대구광역시": "tgk",
    "인천": "ick", "인천광역시": "ick",
    "광주": "kjk", "광주광역시": "kjk",
    "대전": "tjk", "대전광역시": "tjk",
    "울산": "usk", "울산광역시": "usk",
    "세종": "sjk", "세종특별자치시": "sjk",
    "강원": "gak", "강원특별자치도": "gak",
    "충북": "hbk", "충청북도": "hbk",
    "충남": "hck", "충청남도": "hck",
    "전북": "jbk", "전라북도": "jbk",
    "전남": "jnk", "전라남도": "jnk",
    "경북": "gbk", "경상북도": "gbk",
    "경남": "gnk", "경상남도": "gnk",
    "제주": "jjk", "제주특별자치도": "jjk",
}

# 기본값: 발행국/언어/목록전거
COUNTRY_FIXED = "ulk"   # 발행국 기본값
LANG_FIXED    = "kor"   # 언어 기본값

# 008 본문(40자) 조립기 — 단행본 기준(type_of_date 기본 's')
def build_008_kormarc_bk(
    date_entered,          # 00-05 YYMMDD
    date1,                 # 07-10 4자리(예: '2025' / '19uu')
    country3,              # 15-17 3자리
    lang3,                 # 35-37 3자리
    date2="",              # 11-14
    illus4="",             # 18-21 최대 4자(예: 'a','ad','ado'…)
    has_index="0",         # 31 '0' 없음 / '1' 있음
    lit_form=" ",          # 33 (p시/f소설/e수필/i서간문학/m기행·일기·수기)
    bio=" ",               # 34 (a 자서전 / b 전기·평전 / d 부분적 전기)
    type_of_date="s",      # 06
    modified_record=" ",   # 28
    cataloging_src="a",    # 32  ← 기본값 'a'
):
    def pad(s, n, fill=" "):
        s = "" if s is None else str(s)
        return (s[:n] + fill * n)[:n]

    if len(date_entered) != 6 or not date_entered.isdigit():
        raise ValueError("date_entered는 YYMMDD 6자리 숫자여야 합니다.")
    if len(date1) != 4:
        raise ValueError("date1은 4자리여야 합니다. 예: '2025', '19uu'")

    body = "".join([
        date_entered,               # 00-05
        pad(type_of_date,1),        # 06
        date1,                      # 07-10
        pad(date2,4),               # 11-14
        pad(country3,3),            # 15-17
        pad(illus4,4),              # 18-21
        " " * 4,                    # 22-25 (이용대상/자료형태/내용형식) 공백
        " " * 2,                    # 26-27 공백
        pad(modified_record,1),     # 28
        "0",                        # 29 회의간행물
        "0",                        # 30 기념논문집
        has_index if has_index in ("0","1") else "0",  # 31 색인
        pad(cataloging_src,1),      # 32 목록 전거
        pad(lit_form,1),            # 33 문학형식
        pad(bio,1),                 # 34 전기
        pad(lang3,3),               # 35-37 언어
        " " * 2                     # 38-39 (정부기관부호 등) 공백
    ])
    if len(body) != 40:
        raise AssertionError(f"008 length != 40: {len(body)}")
    return body

# 발행연도 추출(알라딘 pubDate 우선)
def extract_year_from_aladin_pubdate(pubdate_str: str) -> str:
    m = re.search(r"(19|20)\d{2}", pubdate_str or "")
    return m.group(0) if m else "19uu"

# 300 발행지 문자열 → country3 추론
def guess_country3_from_place(place_str: str) -> str:
    if not place_str:
        return COUNTRY_FIXED
    for key, code in KR_REGION_TO_CODE.items():
        if key in place_str:
            return code
    # 한국 일반코드("ko ")는 사용하지 않으므로, 기본값으로 통일
    return COUNTRY_FIXED


# ====== 단어 감지 ======
def detect_illus4(text: str) -> str:
    # a: 삽화/일러스트/그림, d: 도표/그래프/차트, o: 사진/화보
    keys = []
    if re.search(r"삽화|삽도|도해|일러스트|일러스트레이션|그림|illustration", text, re.I): keys.append("a")
    if re.search(r"도표|표|차트|그래프|chart|graph", text, re.I):                          keys.append("d")
    if re.search(r"사진|포토|화보|photo|photograph|컬러사진|칼라사진", text, re.I):          keys.append("o")
    out = []
    for k in keys:
        if k not in out:
            out.append(k)
    return "".join(out)[:4]

def detect_index(text: str) -> str:
    return "1" if re.search(r"색인|찾아보기|인명색인|사항색인|index", text, re.I) else "0"

def detect_lit_form(title: str, category: str, extra_text: str = "") -> str:
    blob = f"{title} {category} {extra_text}"
    if re.search(r"서간집|편지|서간문|letters?", blob, re.I): return "i"    # 서간문학
    if re.search(r"기행|여행기|여행 에세이|일기|수기|diary|travel", blob, re.I): return "m"  # 기행/일기/수기
    if re.search(r"시집|산문시|poem|poetry", blob, re.I): return "p"        # 시
    if re.search(r"소설|장편|중단편|novel|fiction", blob, re.I): return "f"  # 소설
    if re.search(r"에세이|수필|essay", blob, re.I): return "e"               # 수필
    return " "

def detect_bio(text: str) -> str:
    if re.search(r"자서전|회고록|autobiograph", text, re.I): return "a"
    if re.search(r"전기|평전|인물 평전|biograph", text, re.I): return "b"
    if re.search(r"전기적|자전적|회고|회상", text): return "d"
    return " "

# 메인: ISBN 하나로 008 생성 (toc/300/041 연동 가능)

def _is_unknown_place(s: str | None) -> bool:
    if not s:
        return False
    t = s.strip()
    t_no_sp = t.replace(" ", "")
    lower = t.lower()
    return (
        "미상" in t or
        "미상" in t_no_sp or
        "unknown" in lower or
        "place unknown" in lower
    )

def build_008_from_isbn(
    isbn: str,
    *,
    aladin_pubdate: str = "",
    aladin_title: str = "",
    aladin_category: str = "",
    aladin_desc: str = "",
    aladin_toc: str = "",            # 목차가 있으면 감지에 활용
    source_300_place: str = "",      # 300 발행지 문자열(있으면 country3 추정)
    override_country3: str = None,   # 외부 모듈이 주면 최우선
    override_lang3: str = None,      # 외부 모듈이 주면 최우선(041)
    cataloging_src: str = "a",       # 32 목록 전거(기본 'a')
):
    today  = datetime.datetime.now().strftime("%y%m%d")  # YYMMDD
    date1  = extract_year_from_aladin_pubdate(aladin_pubdate)

    # country 우선순위: override > 300발행지 매핑 > 기본값 -- 발행지미상인 경우
    if override_country3:
        country3 = override_country3
    elif source_300_place:
        if _is_unknown_place(source_300_place):
            CURRENT_DEBUG_LINES.append(f"[008] 발행지 미상 감지 source_300_place={source_300_place!r} → country3='   '")
            country3 = "   "  # 공백 3칸 유지
        else:
            guessed = guess_country3_from_place(source_300_place)
            # guess 실패 시엔 기본값으로 가지 말고, 최소한 로그 남기기
            if guessed:
                country3 = guessed
            else:
                CURRENT_DEBUG_LINES.append(f"[008] 발행지 매핑 실패 place={source_300_place!r} → 기본값 적용")
                country3 = COUNTRY_FIXED
    else:
        country3 = COUNTRY_FIXED
    
        

    # lang 우선순위: override(041) > 기본값
    lang3 = override_lang3 or LANG_FIXED

    # 단어 감지용 텍스트: 제목 + 소개 + 목차
    bigtext = " ".join([aladin_title or "", aladin_desc or "", aladin_toc or ""])
    illus4    = detect_illus4(bigtext)
    has_index = detect_index(bigtext)
    lit_form  = detect_lit_form(aladin_title or "", aladin_category or "", bigtext)
    bio       = detect_bio(bigtext)

    return build_008_kormarc_bk(
        date_entered=today,
        date1=date1,
        country3=country3,
        lang3=lang3,
        illus4=illus4,
        has_index=has_index,
        lit_form=lit_form,
        bio=bio,
        cataloging_src=cataloging_src,
    )
# ========= 008 생성 블록 v3 끝 =========

# 🔍 키워드 추출 (konlpy 없이)
def extract_keywords_from_text(text, top_n=7):
    words = re.findall(r'\b[\w가-힣]{2,}\b', text)
    filtered = [w for w in words if len(w) > 1]
    freq = Counter(filtered)
    return [kw for kw, _ in freq.most_common(top_n)]

def clean_keywords(words):
    stopwords = {"아주", "가지", "필요한", "등", "위해", "것", "수", "더", "이런", "있다", "된다", "한다"}
    return [w for w in words if w not in stopwords and len(w) > 1]



# 📡 부가기호, SET ISBN 추출 (국립중앙도서관)
@st.cache_data(ttl=24*3600)

def fetch_additional_code_from_nlk(isbn: str) -> dict:
    """
    국립중앙도서관 서지API(서지정보)에서 EA_ADD_CODE(부가기호), SET_ISBN(세트 ISBN))을 함께 가져옴.
    실패 시 각 필드는 빈 문자열로 반환.
    """
    attempts = [
        "https://seoji.nl.go.kr/landingPage/SearchApi.do",
        "https://www.nl.go.kr/seoji/SearchApi.do",
        "http://seoji.nl.go.kr/landingPage/SearchApi.do",
        "http://www.nl.go.kr/seoji/SearchApi.do",
    ]
    params = {
        "cert_key": NLK_CERT_KEY,
        "result_style": "json",
        "page_no": 1,
        "page_size": 1,
        "isbn": isbn.strip().replace("-", ""),
    }

    for base in attempts:
        try:
            r = SESSION.get(base, params=params, timeout=(5, 10))
            r.raise_for_status()

            j = r.json()
            doc = None
            if isinstance(j, dict):
                if "docs" in j and isinstance(j["docs"], list) and j["docs"]:
                    doc = j["docs"][0]
                elif "doc" in j and isinstance(j["doc"], list) and j["doc"]:
                    doc = j["doc"][0]
            if not doc:
                continue

            add_code = (doc.get("EA_ADD_CODE") or "").strip()
            set_isbn = (doc.get("SET_ISBN") or "").strip()
            price = (doc.get("PRE_PRICE") or "").strip()

            return {
                "add_code": add_code,
                "set_isbn": set_isbn,
                "price": price,
            }

        except Exception:
            continue

    # 전부 실패하면 빈 값으로 반환
    return {
        "add_code": "",
        "set_isbn": "",
        "set_title": "",
        "price": "",
    }



# 🔤 언어 감지 및 041, 546 생성
ISDS_LANGUAGE_CODES = {
    'kor': '한국어', 'eng': '영어', 'jpn': '일본어', 'chi': '중국어', 'rus': '러시아어',
    'ara': '아랍어', 'fre': '프랑스어', 'ger': '독일어', 'ita': '이탈리아어', 'spa': '스페인어',
    'und': '알 수 없음'
}

def detect_language(text):
    text = re.sub(r'[\s\W_]+', '', text)
    if not text:
        return 'und'
    first_char = text[0]
    if '\uac00' <= first_char <= '\ud7a3':
        return 'kor'
    elif '\u3040' <= first_char <= '\u30ff':
        return 'jpn'
    elif '\u4e00' <= first_char <= '\u9fff':
        return 'chi'
    elif '\u0400' <= first_char <= '\u04FF':
        return 'rus'
    elif 'a' <= first_char.lower() <= 'z':
        return 'eng'
    else:
        return 'und'

def generate_546_from_041_kormarc(marc_041: str) -> str:
    a_codes, h_code = [], None
    for part in marc_041.split():
        if part.startswith("$a"):
            a_codes.append(part[2:])
        elif part.startswith("$h"):
            h_code = part[2:]
    if len(a_codes) == 1:
        a_lang = ISDS_LANGUAGE_CODES.get(a_codes[0], "알 수 없음")
        if h_code:
            h_lang = ISDS_LANGUAGE_CODES.get(h_code, "알 수 없음")
            return f"{h_lang} 원작을 {a_lang}로 번역"
        else:
            return f"{a_lang}로 씀"
    elif len(a_codes) > 1:
        langs = [ISDS_LANGUAGE_CODES.get(code, "알 수 없음") for code in a_codes]
        return f"{'、'.join(langs)} 병기"
    return "언어 정보 없음"

    has_h = "$h" in (marc_041 or "")
    if not has_h:
        return ""

def crawl_aladin_original_and_price(isbn13):
    url = f"https://www.aladin.co.kr/shop/wproduct.aspx?ISBN={isbn13}"
    headers = {"User-Agent": "Mozilla/5.0"}
    try:
        res = requests.get(url, headers=headers, timeout=10)
        soup = BeautifulSoup(res.text, "html.parser")
        original = soup.select_one("div.info_original")
        price = soup.select_one("span.price2")
        return {
            "original_title": original.text.strip() if original else "",
            "price": price.text.strip().replace("정가 : ", "").replace("원", "").replace(",", "").strip() if price else ""
        }
    except:
        return {}

# ---- 653 전처리 유틸 ----
def _norm(text: str) -> str:
    import re, unicodedata
    if not text:
        return ""
    text = unicodedata.normalize("NFKC", text).lower()
    text = re.sub(r"[^\w\s\uac00-\ud7a3]", " ", text)  # 한/영/숫자/공백만
    return re.sub(r"\s+", " ", text).strip()

def _clean_author_str(s: str) -> str:
    import re
    if not s:
        return ""
    s = re.sub(r"\(.*?\)", " ", s)      # (지은이), (옮긴이) 등 제거
    s = re.sub(r"[/;·,]", " ", s)       # 구분자 공백화
    return re.sub(r"\s+", " ", s).strip()

def _build_forbidden_set(title: str, authors: str) -> set:
    t_norm = _norm(title)
    a_norm = _norm(authors)
    forb = set()
    if t_norm:
        forb.update(t_norm.split())
        forb.add(t_norm.replace(" ", ""))  # '죽음 트릴로지' → '죽음트릴로지'
    if a_norm:
        forb.update(a_norm.split())
        forb.add(a_norm.replace(" ", ""))
    return {f for f in forb if f and len(f) >= 2}  # 1글자 제거

def _should_keep_keyword(kw: str, forbidden: set) -> bool:
    n = _norm(kw)
    if not n or len(n.replace(" ", "")) < 2:
        return False
    for tok in forbidden:
        if tok in n or n in tok:
            return False
    return True
# -------------------------

# 📄 653 필드 키워드 생성
# ② 알라딘 메타데이터 호출 함수
def fetch_aladin_metadata(isbn):
    url = (
        "http://www.aladin.co.kr/ttb/api/ItemLookUp.aspx"
        f"?ttbkey={aladin_key}"
        "&ItemIdType=ISBN"
        f"&ItemId={isbn}"
        "&output=js"
        "&Version=20131101"
        "&OptResult=Toc"
    )
    data = requests.get(url).json()
    item = (data.get("item") or [{}])[0]

    # 저자 필드 다양한 키 대응
    raw_author = item.get("author") or item.get("authors") or item.get("author_t") or ""
    authors = _clean_author_str(raw_author)

    return {
        "category": item.get("categoryName", "") or "",
        "title": item.get("title", "") or "",
        "authors": authors,                           # ⬅️ 추가됨
        "description": item.get("description", "") or "",
        "toc": item.get("toc", "") or "",
    }



# ③ GPT-4 기반 653 생성 함수
def generate_653_with_gpt(category, title, authors, description, toc, max_keywords=7):
    import re

    parts = [p.strip() for p in (category or "").split(">") if p.strip()]
    cat_tail = " ".join(parts[-2:]) if len(parts) >= 2 else (parts[-1] if parts else "")

    forbidden = _build_forbidden_set(title, authors)
    forbidden_list = ", ".join(sorted(forbidden)) or "(없음)"

    # ===== 프롬프트(추상·메타 표현 금지 강화) =====
    system_msg = {
        "role": "system",
        "content": (
            "당신은 KORMARC 작성 경험이 풍부한 도서관 메타데이터 전문가입니다. "
            "주어진 분류 정보, 설명, 목차를 바탕으로 'MARC 653 자유주제어'를 도출합니다.\n\n"
            "원칙\n"
            "- 653은 '검색·발견' 효용을 높이는 명사 중심 주제어로 구성하되, "
            "**모든 주제어는 붙여쓰기 형태(공백 없음)**로 작성합니다. 예: '아동문학', '정서조절', '시간관리', '인지과학'\n"
            "- 서명(245)·저자(100/700)에서 나온 단어/표현(활용형 포함)과 시리즈명, 출판사명, 판·쇄, 연도, 페이지수, 가격, 수상, 홍보문구를 제외합니다.\n"
            "- 너무 일반적이거나 기능이 약한 표현은 제외합니다. "
            "예: 연구, 개론, 방법, 사례, 고찰, 문제, 개정판, 서문, 목차, 참고문헌, 저자, 번역, 추천사, 베스트셀러, 안내, 소개, 이론\n"
            "- **추상·평가·메타 표현은 절대 사용하지 마세요.** "
            "예: 사회적의의, 의의, 시사점, 의의와한계, 배경, 개관, 개요, 현황, 동향, 의미, 정리, 결론, 서사분석(일반), 비평(일반)\n"
            "- 위와 같은 표현이 떠오르면 반드시 책의 실제 주제를 드러내는 **구체 하위개념**으로 치환합니다. "
            "예: '사회적의의' → (금지) / '식민경험', '이민정체성', '도시화서사', '광둥어문학', '홍콩근현대사' 등\n"
            "- 상·하위 분류가 주어지면, 주제의 '구체성'을 반영합니다(가능하면 2~6글자 복합명사 위주).\n\n"
            "선정 기준(출력하지 마세요)\n"
            "- 관련성: 책의 핵심 주제를 직접 설명하는가?\n"
            "- 구체성: 포괄어(심리학, 철학)보다 하위 개념(정서조절, 실존주의)을 선호.\n"
            "- 비중복성: 의미가 겹치거나 형태만 다른 후보는 하나로 대표.\n"
            "- 균형: 분류·설명·목차의 균형을 추구.\n\n"
            "출력 형식\n"
            f"- 한 줄, 다음과 같이 출력: `$a키워드1 $a키워드2 $a키워드3 ...` (최대 {max_keywords}개 이내)\n"
            "- 띄어쓰기 없이 한글 명사로만 구성하며, 쉼표/번호/괄호/줄바꿈/불필요한 문장 금지.\n\n"
            "충분 정보가 없을 때\n"
            "- 분류의 마지막 1~2개 요소를 반영하고, 설명·목차에서 핵심 개념을 보수적으로 선별하세요.\n"
            "- 생각 과정은 출력하지 말고, 최종 결과만 형식대로 제공합니다."
        )
    }

    user_msg = {
        "role": "user",
        "content": (
            f"아래 정보를 바탕으로 최대 {max_keywords}개의 MARC 653 주제어를 한 줄로 출력해 주세요.\n\n"
            f"- 분류(전체 체인): \"{category}\"\n"
            f"- 분류(핵심 꼬리): \"{cat_tail}\"\n"
            f"- 제목(245): \"{title}\"\n"
            f"- 저자(100/700): \"{authors}\"\n"
            f"- 설명: \"{description}\"\n"
            f"- 목차: \"{toc}\"\n"
            f"- 제외어 목록(서명/저자 유래, 정규화 포함): {forbidden_list}\n\n"
            "지시사항:\n"
            "1) '제목'·'저자'에서 유래한 단어·표현, 시리즈·출판사·판차·연도 등 비주제 요소는 절대 포함하지 마세요.\n"
            "2) 분류·설명·목차에서 핵심 주제를 명사 중심(2~6글자 복합명사)으로 선택하고 **띄어쓰기를 모두 제거**하세요. "
            "예: '자기계발', '감정조절', '지속가능성', '시간관리'\n"
            "3) 너무 일반적 표현(연구, 방법, 사례, 고찰, 안내, 소개, 이론 등)과 **추상·평가·메타 표현(사회적의의, 의의, 시사점, 배경, 개관, 개요, 현황, 동향, 의미 등)**은 제외하세요.\n"
            "4) 중복이나 동의어는 하나만 남기고 더 구체적인 표현을 선택하세요. "
            "추상표현이 떠오르면 책의 실제 주제를 드러내는 구체 하위개념으로 치환하세요.\n"
            "5) 출력은 오직 다음 형식 한 줄: `$a키워드1 $a키워드2 ...` (공백은 각 $a 사이에만)\n\n"
            "이제 결과를 출력하세요."
        )
    }
    # ================================================

    try:
        resp = client.chat.completions.create(
            model="gpt-4o",
            messages=[system_msg, user_msg],
            temperature=0.2,
            max_tokens=180,
        )
        raw = (resp.choices[0].message.content or "").strip()

        pattern = re.compile(r"\$a(.*?)(?=(?:\$a|$))", re.DOTALL)
        kws = [m.group(1).strip() for m in pattern.finditer(raw)]
        if not kws:
            tmp = re.split(r"[,\n;|/·]", raw)
            kws = [t.strip().lstrip("$a") for t in tmp if t.strip()]

        # 붙여쓰기
        kws = [kw.replace(" ", "") for kw in kws if kw]

        # 금칙어 필터
        kws = [kw for kw in kws if _should_keep_keyword(kw, forbidden)]

        # 정규화 중복 제거
        seen = set(); uniq = []
        for kw in kws:
            n = _norm(kw)
            if n not in seen:
                seen.add(n); uniq.append(kw)

        uniq = uniq[:max_keywords]
        return "".join(f"$a{kw}" for kw in uniq)

    except Exception as e:
        st.warning(f"⚠️ 653 주제어 생성 실패: {e}")
        return None
 

def _lang3_from_tag041(tag_041: str | None) -> str | None:
    """'041 $akor$hrus'에서 첫 $a만 뽑아 008 lang3 override에 사용."""
    if not tag_041: return None
    m = re.search(r"\$a([a-z]{3})", tag_041, flags=re.I)
    return m.group(1).lower() if m else None

def _build_020_from_item_and_nlk(isbn: str, item: dict) -> str:
    """020 $a$g(:$c) — NLK 부가기호를 $c(가격)보다 앞에 배치"""
    # 1) 알라딘 가격
    price = str((item or {}).get("priceStandard", "") or "").strip()

    # 2) NLK에서 부가기호 + 가격 가져오기
    try:
        nlk_extra = fetch_additional_code_from_nlk(isbn) or {}
        add_code = nlk_extra.get("add_code", "")
        price_from_nlk = nlk_extra.get("price", "")
    except Exception:
        add_code = ""
        price_from_nlk = ""

    # 3) 가격 우선순위: 알라딘 → NLK
    final_price = price or price_from_nlk

    # 4) 조합
    parts = [f"=020  \\\\$a{isbn}"]
    if add_code:
        parts.append(f"$g{add_code}")
    if final_price:
        parts.append(f":$c{final_price}")

    return "".join(parts)



def _build_653_via_gpt(item: dict) -> str | None:
    """네가 올린 generate_653_with_gpt() 그대로 활용해서 653 한 줄 반환."""
    title = (item or {}).get("title","") or ""
    category = (item or {}).get("categoryName","") or ""
    raw_author = (item or {}).get("author","") or ""
    desc = (item or {}).get("description","") or ""
    toc  = ((item or {}).get("subInfo",{}) or {}).get("toc","") or ""

    kwline = generate_653_with_gpt(
        category=category,
        title=title,
        authors=_clean_author_str(raw_author),
        description=desc,
        toc=toc,
        max_keywords=7
    )
    # kwline이 "$a키워드$a..." 형태라고 가정
    return f"=653  \\\\{kwline.replace(' ', '')}" if kwline else None

def _parse_653_keywords(tag_653: str | None) -> list[str]:
    """
    '=653  \\$a아동문학$a정서조절$a시간관리' → ['아동문학','정서조절','시간관리']
    공백/빈값 제거 + 최대 7개 반환.
    """
    if not tag_653:
        return []
    s = tag_653.strip()

    # 접두부 정리
    s = re.sub(r"^=653\s+\\\\", "", s)

    # $a 서브필드 추출
    kws = []
    for m in re.finditer(r"\$a([^$]+)", s):
        w = (m.group(1) or "").strip()
        if w:
            kws.append(w)

    # 중복 제거 + 상한
    seen, out = set(), []
    for w in kws:
        if w not in seen:
            seen.add(w)
            out.append(w)
        if len(out) >= 7:
            break
    return out


# --- 가격 추출 헬퍼: 알라딘 priceStandard 우선, 없으면 크롤링 백업 ---
def _extract_price_kr(item: dict, isbn: str) -> str:
    # 1) 알라딘 표준가 우선
    raw = str((item or {}).get("priceStandard", "") or "").strip()
    # 2) 비어 있으면 크롤링 백업 시도
    if not raw:
        try:
            crawl = crawl_aladin_original_and_price(isbn) or {}
            raw = crawl.get("price", "").strip()
        except Exception:
            raw = ""
    # 3) 숫자만 남기기
    import re
    digits = re.sub(r"[^\d]", "", raw)
    return digits  # "15000" 같은 형태

# --- 950 빌더 ---
def build_950_from_item_and_price(item: dict, isbn: str) -> str:
    price = _extract_price_kr(item, isbn)
    if not price:
        return ""  # 가격 없으면 950 생략
    return f"=950  0\\$b\\{price}"

# =========================
# --- 구글시트 로드 & 캐시 관리 ---
# =========================
@st.cache_data(ttl=3600)
def load_publisher_db():
    creds = ServiceAccountCredentials.from_json_keyfile_dict(st.secrets["gspread"], 
                                                            ["https://spreadsheets.google.com/feeds",
                                                             "https://www.googleapis.com/auth/drive"])
    client = gspread.authorize(creds)
    sh = client.open("출판사 DB")
    
    # KPIPA_PUB_REG: 번호, 출판사명, 주소, 전화번호 → 출판사명, 주소만 사용
    pub_rows = sh.worksheet("발행처명–주소 연결표").get_all_values()[1:]
    pub_rows_filtered = [row[1:3] for row in pub_rows]  # 출판사명, 주소
    publisher_data = pd.DataFrame(pub_rows_filtered, columns=["출판사명", "주소"])
    
    # 008: 발행국 발행국 부호 → 첫 2열만
    region_rows = sh.worksheet("발행국명–발행국부호 연결표").get_all_values()[1:]
    region_rows_filtered = [row[:2] for row in region_rows]
    region_data = pd.DataFrame(region_rows_filtered, columns=["발행국", "발행국 부호"])
    
    # IM_* 시트: 출판사/임프린트 하나의 칼럼
    imprint_frames = []
    for ws in sh.worksheets():
        if ws.title.startswith("발행처-임프린트 연결표"):
            data = ws.get_all_values()[1:]
            imprint_frames.extend([row[0] for row in data if row])
    imprint_data = pd.DataFrame(imprint_frames, columns=["임프린트"])
    
    return publisher_data, region_data, imprint_data

# =========================
# --- 알라딘 API ---
# =========================
def search_aladin_by_isbn(isbn):
    try:
        ttbkey = st.secrets["aladin"]["ttbkey"]
        url = "https://www.aladin.co.kr/ttb/api/ItemLookUp.aspx"
        params = {"ttbkey": ttbkey, "itemIdType": "ISBN", "ItemId": isbn, 
                  "output": "js", "Version": "20131101"}
        res = requests.get(url, params=params, timeout=15)
        res.raise_for_status()
        data = res.json()
        if "item" not in data or not data["item"]:
            return None, f"도서 정보를 찾을 수 없습니다. [응답: {data}]"
        book = data["item"][0]
        title = book.get("title", "제목 없음")
        author = book.get("author", "")
        publisher = book.get("publisher", "출판사 정보 없음")
        pubdate = book.get("pubDate", "")
        pubyear = pubdate[:4] if len(pubdate) >= 4 else "발행년도 없음"
        authors = [a.strip() for a in author.split(",")] if author else []
        creator_str = " ; ".join(authors) if authors else "저자 정보 없음"
        field_245 = f"=245  10$a{title} /$c{creator_str}"
        return {"title": title, "creator": creator_str, "publisher": publisher, "pubyear": pubyear, "245": field_245}, None
    except Exception as e:
        return None, f"Aladin API 예외: {e}"

# =========================
# --- 정규화 함수 ---
# =========================
def normalize_publisher_name(name):
    return re.sub(r"\s|\(.*?\)|주식회사|㈜|도서출판|출판사", "", name).lower()

def normalize_stage2(name):
    name = re.sub(r"(주니어|JUNIOR|어린이|키즈|북스|아이세움|프레스)", "", name, flags=re.IGNORECASE)
    eng_to_kor = {"springer": "스프링거", "cambridge": "케임브리지", "oxford": "옥스포드"}
    for eng, kor in eng_to_kor.items():
        name = re.sub(eng, kor, name, flags=re.IGNORECASE)
    return name.strip().lower()

def split_publisher_aliases(name):
    aliases = []
    bracket_contents = re.findall(r"\((.*?)\)", name)
    for content in bracket_contents:
        parts = re.split(r"[,/]", content)
        parts = [p.strip() for p in parts if p.strip()]
        aliases.extend(parts)
    name_no_brackets = re.sub(r"\(.*?\)", "", name).strip()
    if "/" in name_no_brackets:
        parts = [p.strip() for p in name_no_brackets.split("/") if p.strip()]
        rep_name = parts[0]
        aliases.extend(parts[1:])
    else:
        rep_name = name_no_brackets
    return rep_name, aliases

def normalize_publisher_location_for_display(location_name):
    if not location_name or location_name in ("출판지 미상", "예외 발생"):
        return location_name
    location_name = location_name.strip()
    major_cities = ["서울", "인천", "대전", "광주", "울산", "대구", "부산", "세종"]
    for city in major_cities:
        if city in location_name:
            return location_name[:2]
    parts = location_name.split()
    loc = parts[1] if len(parts) > 1 else parts[0]
    if loc.endswith("시"):
        loc = loc[:-1]
    return loc

# =========================
# --- KPIPA DB 검색 보조 함수 ---
# =========================
def search_publisher_location_with_alias(name, publisher_data):
    debug_msgs = []
    if not name:
        return "출판지 미상", ["❌ 검색 실패: 입력된 출판사명이 없음"]
    norm_name = normalize_publisher_name(name)
    candidates = publisher_data[publisher_data["출판사명"].apply(lambda x: normalize_publisher_name(x)) == norm_name]
    if not candidates.empty:
        address = candidates.iloc[0]["주소"]
        debug_msgs.append(f"✅ KPIPA DB 매칭 성공: {name} → {address}")
        return address, debug_msgs
    else:
        debug_msgs.append(f"❌ KPIPA DB 매칭 실패: {name}")
        return "출판지 미상", debug_msgs

# =========================
# --- IM 임프린트 보조 함수 ---
# =========================
def find_main_publisher_from_imprints(rep_name, imprint_data, publisher_data):
    """
    IM_* 시트에서 임프린트명을 검색하고, KPIPA DB에서 해당 출판사명으로 주소를 반환
    """
    norm_rep = normalize_publisher_name(rep_name)
    for full_text in imprint_data["임프린트"]:
        if "/" in full_text:
            pub_part, imprint_part = [p.strip() for p in full_text.split("/", 1)]
        else:
            pub_part, imprint_part = full_text.strip(), None

        if imprint_part:
            norm_imprint = normalize_publisher_name(imprint_part)
            if norm_imprint == norm_rep:
                # KPIPA DB에서 pub_part를 검색
                location, debug_msgs = search_publisher_location_with_alias(pub_part, publisher_data)
                return location, debug_msgs
    return None, [f"❌ IM DB 검색 실패: 매칭되는 임프린트 없음 ({rep_name})"]

    

# =========================
# --- KPIPA 페이지 검색 ---
# =========================
def get_publisher_name_from_isbn_kpipa(isbn):
    search_url = "https://bnk.kpipa.or.kr/home/v3/addition/search"
    params = {"ST": isbn, "PG": 1, "PG2": 1, "DSF": "Y", "SO": "weight", "DT": "A"}
    headers = {"User-Agent": "Mozilla/5.0"}
    def normalize(name):
        return re.sub(r"\s|\(.*?\)|주식회사|㈜|도서출판|출판사|프레스", "", name).lower()
    try:
        res = requests.get(search_url, params=params, headers=headers, timeout=15)
        res.raise_for_status()
        soup = BeautifulSoup(res.text, "html.parser")
        first_result_link = soup.select_one("a.book-grid-item")
        if not first_result_link:
            return None, None, "❌ 검색 결과 없음 (KPIPA)"
        detail_href = first_result_link.get("href")
        detail_url = f"https://bnk.kpipa.or.kr{detail_href}"
        detail_res = requests.get(detail_url, headers=headers, timeout=15)
        detail_res.raise_for_status()
        detail_soup = BeautifulSoup(detail_res.text, "html.parser")
        pub_info_tag = detail_soup.find("dt", string="출판사 / 임프린트")
        if not pub_info_tag:
            return None, None, "❌ '출판사 / 임프린트' 항목을 찾을 수 없습니다. (KPIPA)"
        dd_tag = pub_info_tag.find_next_sibling("dd")
        if dd_tag:
            full_text = dd_tag.get_text(strip=True)
            publisher_name_full = full_text
            publisher_name_part = publisher_name_full.split("/")[0].strip()
            publisher_name_norm = normalize(publisher_name_part)
            return publisher_name_full, publisher_name_norm, None
        return None, None, "❌ 'dd' 태그에서 텍스트를 추출할 수 없습니다. (KPIPA)"
    except Exception as e:
        return None, None, f"KPIPA 예외: {e}"

# =========================
# ----발행국 부호 찾기-----
# =========================

def get_country_code_by_region(region_name, region_data):
    """
    지역명을 기반으로 008 발행국 부호를 찾음.
    region_data: DataFrame, columns=["발행국", "발행국 부호"]
    """
    try:
        def normalize_region_for_code(region):
            region = (region or "").strip()
            if region.startswith(("전라", "충청", "경상")):
                return region[0] + (region[2] if len(region) > 2 else "")
            return region[:2]
        normalized_input = normalize_region_for_code(region_name)
        for idx, row in region_data.iterrows():
            sheet_region, country_code = row["발행국"], row["발행국 부호"]
            if normalize_region_for_code(sheet_region) == normalized_input:
                return country_code.strip() or "   "

        return "   "
    except Exception as e:
        st.write(f"⚠️ get_country_code_by_region 예외: {e}")
        return "   "

# =========================
# --- 문체부 검색 ---
# =========================
def get_mcst_address(publisher_name):
    url = "https://book.mcst.go.kr/html/searchList.php"
    params = {"search_area": "전체", "search_state": "1", "search_kind": "1", 
              "search_type": "1", "search_word": publisher_name}
    debug_msgs = []
    try:
        res = requests.get(url, params=params, timeout=15)
        res.raise_for_status()
        soup = BeautifulSoup(res.text, "html.parser")
        results = []
        for row in soup.select("table.board tbody tr"):
            cols = row.find_all("td")
            if len(cols) >= 4:
                reg_type = cols[0].get_text(strip=True)
                name = cols[1].get_text(strip=True)
                address = cols[2].get_text(strip=True)
                status = cols[3].get_text(strip=True)
                if status == "영업":
                    results.append((reg_type, name, address, status))
        if results:
            debug_msgs.append(f"[문체부] 검색 성공: {len(results)}건")
            return results[0][2], results, debug_msgs
        else:
            debug_msgs.append("[문체부] 검색 결과 없음")
            return "미확인", [], debug_msgs
    except Exception as e:
        debug_msgs.append(f"[문체부] 예외 발생: {e}")
        return "오류 발생", [], debug_msgs

def build_pub_location_bundle(isbn, publisher_name_raw):
    debug = []
    try:
        publisher_data, region_data, imprint_data = load_publisher_db()
        debug.append("✓ 구글시트 DB 적재 성공")

        kpipa_full, kpipa_norm, err = get_publisher_name_from_isbn_kpipa(isbn)
        if err: debug.append(f"KPIPA 검색: {err}")

        rep_name, aliases = split_publisher_aliases(kpipa_full or publisher_name_raw or "")
        resolved_pub_for_search = rep_name or (publisher_name_raw or "").strip()
        debug.append(f"대표 출판사명 추정: {resolved_pub_for_search} | ALIAS: {aliases}")

        place_raw, msgs = search_publisher_location_with_alias(resolved_pub_for_search, publisher_data)
        debug += msgs
        source = "KPIPA_DB"

        if place_raw in ("출판지 미상", "예외 발생", None):
            place_raw, msgs = find_main_publisher_from_imprints(resolved_pub_for_search, imprint_data, publisher_data)
            debug += msgs
            if place_raw: source = "IMPRINT→KPIPA"

        if not place_raw or place_raw in ("출판지 미상", "예외 발생"):
            mcst_addr, mcst_rows, mcst_dbg = get_mcst_address(resolved_pub_for_search)
            debug += mcst_dbg
            if mcst_addr not in ("미확인", "오류 발생", None):
                place_raw, source = mcst_addr, "MCST"

        if not place_raw or place_raw in ("출판지 미상", "예외 발생", "미확인", "오류 발생"):
            place_raw, source = "출판지 미상", "FALLBACK"
            debug.append("⚠️ 모든 경로 실패 → '출판지 미상'")

        place_display = normalize_publisher_location_for_display(place_raw)
        country_code = get_country_code_by_region(place_raw, region_data)

        return {
            "place_raw": place_raw,
            "place_display": place_display,
            "country_code": country_code,
            "resolved_publisher": resolved_pub_for_search,
            "source": source,
            "debug": debug,
        }
    except Exception as e:
        return {
            "place_raw": "발행지 미상",
            "place_display": "발행지 미상",
            "country_code": "   ",
            "resolved_publisher": publisher_name_raw or "",
            "source": "ERROR",
            "debug": [f"예외: {e}"],
        }

def build_260(place_display: str, publisher_name: str, pubyear: str):
    place = (place_display or "발행지 미상")
    pub = (publisher_name or "발행처 미상")
    year = (pubyear or "발행년 미상")
    return f"=260  \\\\$a{place} :$b{pub},$c{year}"

def _today_yymmdd():
    return datetime.now().strftime("%y%m%d")

def _derive_date1(pubyear: str) -> str:
    y = (pubyear or "").strip()
    return y[:4] if re.fullmatch(r"\d{4}", y) else "19uu"

# ==========================================================================================
# 056 단독 코드
# ==========================================================================================

@dataclass
class BookInfo:
    title: str = ""
    author: str = ""
    pub_date: str = ""
    publisher: str = ""
    isbn13: str = ""
    category: str = ""
    description: str = ""
    toc: str = ""
    extra: Optional[Dict[str, Any]] = None
# ───────── 유틸 ─────────
def clean_text(s: Optional[str]) -> str:
    if not s:
        return ""
    s = html.unescape(s)
    s = re.sub(r"\s+", " ", s).strip()
    return s
def first_match_number(text: str) -> Optional[str]:
    """KDC 숫자만 추출: 0~999 또는 소수점 포함(예: 813.7)"""
    if not text:
        return None
    m = re.search(r"\b([0-9]{1,3}(?:\.[0-9]+)?)\b", text)
    return m.group(1) if m else None
    
    # ⬇️ 추가: 소수점 응답을 받아도 정수부만 반환
def normalize_kdc_3digit(code: Optional[str]) -> Optional[str]:
    """
    입력 예: '813.7', '813', '81', '5', 'KDC 325.1'
    출력 예: '813', '813', '81', '5', '325'  (선행 1~3자리 정수부만)
    """
    if not code:
        return None
    m = re.search(r"(\d{1,3})", code)
    return m.group(1) if m else None
    
def first_or_empty(lst):
    return lst[0] if lst else ""
def strip_tags(html_text: str) -> str:
    return re.sub(r"<[^>]+>", " ", html_text)
# ───────── 1) 알라딘 API 우선 ─────────
def aladin_lookup_by_api(isbn13: str, ttbkey: str) -> Optional[BookInfo]:
    if not ttbkey:
        return None
    params = {
        "ttbkey": ttbkey,
        "itemIdType": "ISBN13",
        "ItemId": isbn13,
        "output": "js",
        "Version": "20131101",
        "OptResult": "authors,categoryName,fulldescription,toc,packaging,ratings"
    }
    try:
        r = requests.get("https://www.aladin.co.kr/ttb/api/ItemLookUp.aspx", params=params, headers=HEADERS, timeout=15)
        r.raise_for_status()
        data = r.json()
        items = data.get("item", [])
        if not items:
            # 디버그: API가 비어있으면 이유를 화면에서 확인할 수 있게
            st.info("알라딘 API(ItemLookUp)에서 결과 없음 → 스크레이핑 백업 시도")
            return None
        it = items[0]
        return BookInfo(
            title=clean_text(it.get("title")),
            author=clean_text(it.get("author")),
            pub_date=clean_text(it.get("pubDate")),
            publisher=clean_text(it.get("publisher")),
            isbn13=clean_text(it.get("isbn13")) or isbn13,
            category=clean_text(it.get("categoryName")),
            description=clean_text(it.get("fulldescription")) or clean_text(it.get("description")),
            toc=clean_text(it.get("toc")),
            extra=it,
        )
    except Exception as e:
        st.info(f"알라딘 API 호출 예외 → {e} / 스크레이핑 백업 시도")
        return None
# ───────── 2) 알라딘 웹 스크레이핑(백업) ─────────
def aladin_lookup_by_web(isbn13: str) -> Optional[BookInfo]:
    try:
        # 검색 URL (Book 타겟 우선)
        params = {"SearchTarget": "Book", "SearchWord": f"isbn:{isbn13}"}
        sr = requests.get(ALADIN_SEARCH_URL, params=params, headers=HEADERS, timeout=15)
        sr.raise_for_status()
        soup = BeautifulSoup(sr.text, "html.parser")
        # 1) 가장 안정적인 카드 타이틀 링크 (a.bo3)
        link_tag = soup.select_one("a.bo3")
        item_url = None
        if link_tag and link_tag.get("href"):
            item_url = urllib.parse.urljoin("https://www.aladin.co.kr", link_tag["href"])
        # 2) 백업: 정규식으로 wproduct 링크 잡기(쌍/홑따옴표 모두)
        if not item_url:
            m = re.search(r'href=[\'"](/shop/wproduct\.aspx\?ItemId=\d+[^\'"]*)[\'"]', sr.text, re.I)
            if m:
                item_url = urllib.parse.urljoin("https://www.aladin.co.kr", html.unescape(m.group(1)))
        # 3) 그래도 없으면, 첫 상품 카드 내 다른 링크 시도
        if not item_url:
            first_card = soup.select_one(".ss_book_box, .ss_book_list")
            if first_card:
                a = first_card.find("a", href=True)
                if a:
                    item_url = urllib.parse.urljoin("https://www.aladin.co.kr", a["href"])
        if not item_url:
            st.warning("알라딘 검색 페이지에서 상품 링크를 찾지 못했습니다.")
            with st.expander("디버그: 검색 페이지 HTML 일부"):
                st.code(sr.text[:2000])
            return None
        # 상품 상세 페이지 요청
        pr = requests.get(item_url, headers=HEADERS, timeout=15)
        pr.raise_for_status()
        psoup = BeautifulSoup(pr.text, "html.parser")
        # 메타 태그로 기본 정보 확보
        og_title = psoup.select_one('meta[property="og:title"]')
        og_desc  = psoup.select_one('meta[property="og:description"]')
        title = clean_text(og_title["content"]) if og_title and og_title.has_attr("content") else ""
        desc  = clean_text(og_desc["content"]) if og_desc and og_desc.has_attr("content") else ""
        # 본문 텍스트 백업(길이 제한)
        body_text = clean_text(psoup.get_text(" "))[:4000]
        description = desc or body_text
        # 저자/출판사/출간일 추출(있으면)
        author = ""
        publisher = ""
        pub_date = ""
        cat_text = ""
        # 상품 정보 표에서 키워드로 추출 시도
        info_box = psoup.select_one("#Ere_prod_allwrap, #Ere_prod_mconts_wrap, #Ere_prod_titlewrap")
        if info_box:
            text = clean_text(info_box.get_text(" "))
            # 아주 느슨한 패턴(있을 때만 잡힘)
            m_author = re.search(r"(저자|지은이)\s*:\s*([^\|·/]+)", text)
            m_publisher = re.search(r"(출판사)\s*:\s*([^\|·/]+)", text)
            m_pubdate = re.search(r"(출간일|출판일)\s*:\s*([0-9]{4}\.[0-9]{1,2}\.[0-9]{1,2})", text)
            if m_author:   author   = clean_text(m_author.group(2))
            if m_publisher: publisher = clean_text(m_publisher.group(2))
            if m_pubdate:  pub_date = clean_text(m_pubdate.group(2))
        # 카테고리(빵부스러기) 시도
        crumbs = psoup.select(".location, .path, .breadcrumb")
        if crumbs:
            cat_text = clean_text(" > ".join(c.get_text(" ") for c in crumbs))
        # 디버그: 어느 링크로 들어갔는지/타이틀 확인
        with st.expander("디버그: 스크레이핑 진입 URL / 파싱 결과"):
            st.write({"item_url": item_url, "title": title})
        
        return BookInfo(
            title=title,
            description=description,
            isbn13=isbn13,
            author=author,
            publisher=publisher,
            pub_date=pub_date,
            category=cat_text
        )
    except Exception as e:
        st.error(f"웹 스크레이핑 예외: {e}")
        return None
# --- 041 원작언어 기반 문학 분류 재정렬(후처리) ---------------------------------
def _parse_marc_041_original(marc041: str):
    """
    MARC 041에서 원작 언어($h)를 3글자 코드로 추출.
    예: '041 0\\$akor$heng' -> 'eng'
    """
    if not marc041:
        return None
    s = str(marc041).lower()
    import re
    m = re.search(r"\$h([a-z]{3})", s)
    return m.group(1) if m else None
def _lang3_to_kdc_lit_base(lang3: str):
    """
    원작 언어코드 -> 문학 계열(8xx) 매핑.
    """
    if not lang3:
        return None
    l = lang3.lower()
    if l in {"eng"}: return "840"  # 영미문학
    if l in {"kor"}: return "810"  # 한국문학
    if l in {"chi", "zho"}: return "820"  # 중국문학 (홍콩/대만 포함)
    if l in {"jpn"}: return "830"  # 일본문학
    if l in {"deu", "ger"}: return "850"  # 독일문학
    if l in {"fre"}: return "860"  # 프랑스문학
    if l in {"spa", "por"}: return "870"  # 스페인/포르투갈문학
    if l in {"ita"}: return "880"  # 이탈리아문학
    return "890"  # 기타 제문학
def _rebase_8xx_with_language(code: str, marc041: str) -> str:
    """
    code가 문학(8xx)이면, 041 $h(원작언어)에 따라 81x/82x/83x/84x…의 '앞 두 자리'를 재정렬.
    - 장르(일의자리)와 소수점은 그대로 보존
    - 041이 없거나 $h 미존재면 원본 유지
    """
    if not code or len(code) < 3 or code[0] != "8":
        return code  # 문학이 아니면 그대로
    orig = _parse_marc_041_original(marc041 or "")
    base = _lang3_to_kdc_lit_base(orig) if orig else None
    if not base:
        return code
    import re
    m = re.match(r"^(\d{3})(\..+)?$", code)
    if not m:
        return code
    head3, tail = m.group(1), (m.group(2) or "")
    genre = head3[2]  # 세번째 자리: 시/희곡/소설/…
    new_head3 = base[:2] + genre
    return new_head3 + tail
# ---------------------------------------------------------------------------
# ───────── 3) 챗G에게 'KDC 숫자만' 요청 (직접분류추천 지원 버전) ─────────
def ask_llm_for_kdc(book: BookInfo, api_key: str, model: str = DEFAULT_MODEL,
                    keywords_hint: list[str] | None = None) -> Optional[str]:
    """
    KDC(056) 판단용 LLM 호출 (C전략)
    - '직접분류추천' 안전장치: 확신이 없으면 이 문자열을 그대로 출력하도록 유도
    - 입력 축약, 2단계 폴백, 파싱 보강 포함
    - 반환: '숫자만'(예: '823','813.7') 또는 '직접분류추천'
    """
    if model is None:
        try:
            model = (st.secrets.get("openai", {}) or {}).get("model", "")
        except Exception:
            model = ""
        if not model:
            model = "gpt-4o-mini"
    # 입력 축약(너무 긴 텍스트로 인한 실패 방지)
    def clip(s: str, n: int) -> str:
        if not s:
            return ""
        s = str(s).strip()
        return s if len(s) <= n else s[:n] + "…"
    title = clip(book.title, 160)
    author = clip(book.author, 120)
    category = clip(book.category, 160)
    description = clip(book.description, 1200)
    toc = clip(book.toc, 1200)
    # 공통 페이로드
    payload = {
        "title": title,
        "author": author,
        "publisher": book.publisher,
        "pub_date": book.pub_date,
        "isbn13": book.isbn13,
        "category": category,
        "description": description,
        "toc": toc,
    }
    # 메인 시스템 프롬프트 (C안 + 강목표 + 세분 규칙 + '직접분류추천' 규정)
    sys_prompt = (
        "너는 한국십진분류법(KDC) 전문가이자 공공도서관 분류 사서이다.\n"
        "입력된 도서 정보를 바탕으로 이 책의 **주제 중심 분류기호(KDC 번호)**를 한 줄로 판단하라.\n\n"
        "참고로, 국립중앙도서관 KOLISNet의 실제 분류 사례를 간접적으로 참조하라. "
        "비슷한 책이 821(중국시)·823(중국소설)·833(일본소설)·843(영미소설) 등으로 분류되는 관행을 고려하되, "
        "현재 도서의 주제와 일치하는 하나의 번호만 선택하라. (웹에 직접 접속하지 말고 사고의 기준으로만 삼는다.)\n\n"
        "규칙:\n"
        "1. 반드시 **소수점 없이 3자리 정수만** 출력한다. 예: 813 / 325 / 005 / 181\n"
        "2. 세목(소수점 이하) 판단은 내부 결정에만 활용하고, **출력은 상위 3자리 정수**로 제한한다.\n"
        "3. 설명, 이유, 접두어, 단위(예: KDC, 분류번호) 등은 출력하지 않는다.\n"
        "4. 한 책이 여러 주제를 다루더라도 **가장 중심되는 주제**를 선택한다.\n"
        "5. 내용이 학문적일 경우, '학문 분야' 기준으로 판단한다. (예: 교양심리서 → 181)\n"
        "6. 특정 **시대·장르** 표기가 분명하더라도 **출력은 상위 3자리 정수**로 한다. "
        "(아동문학·SF 등 장르문학은 먼저 **언어/지역** 계열을 판정한 뒤 문학 분기 상위 3자리로 결정한다. 예: 한국소설 → 813)\n"
        "7. 추상 표현(사회적의의, 현황, 연구, 문제, 방법론 등)은 분류 근거가 아니다.\n"
        "8. ISBN·출판사·카테고리는 보조 신호로만 사용한다.\n"
        "8-1. `keywords_hint_653`가 제공되면 약한 보조 신호로만 참고하고, 설명/목차/범주 증거와 충돌하면 본문 근거를 우선한다.\n"
        "9. 확신이 없으면 가장 관련 범주의 기본 기호(예: 철학→100, 문학→800)를 고려하되, "
        "그래도 확정이 어려우면 **정확히 '직접분류추천'** 네 글자만 출력한다.\n\n"
        "[KDC 강목표 (10단위)]\n"
        "000 총류\n010 도서학 서지학\n020 문헌정보학\n030 백과사전\n040 강연집 수필집 연설문집\n050 일반 연속간행물\n"
        "060 일반 학회 단체 협회 기관 연구기관\n070 신문 저널리즘\n080 일반 전집 총서\n090 향토자료\n100 철학\n110 형이상학\n"
        "120 인식론 인과론 인간학\n130 철학의 체계\n140 경학\n150 동양철학 동양사상\n160 서양철학\n170 논리학\n180 심리학\n"
        "190 윤리학 도덕철학\n200 종교\n210 비교종교\n220 불교\n230 기독교\n240 도교\n250 천도교\n270 힌두교 브라만교\n"
        "280 이슬람교 회교\n290 기타 제종교\n300 사회과학\n310 통계자료\n320 경제학\n330 사회학 사회문제\n340 정치학\n350 행정학\n"
        "360 법률 법학\n370 교육학\n380 풍습 예절 민속학\n390 국방 군사학\n400 자연과학\n410 수학\n420 물리학\n430 화학\n440 천문학\n"
        "450 지학\n460 광물학\n470 생명과학\n480 식물학\n490 동물학\n500 기술과학\n510 의학\n520 농업 농학\n530 공학 공업일반 토목공학 환경공학\n"
        "540 건축 건축학\n550 기계공학\n560 전기공학 통신공학 전자공학\n570 화학공학\n580 제조업\n590 생활과학\n600 예술\n620 조각 조형미술\n"
        "630 공예\n640 서예\n650 회화 도화 디자인\n660 사진예술\n670 음악\n680 공연예술 매체예술\n690 오락 스포츠\n700 언어\n710 한국어\n"
        "720 중국어\n730 일본어 및 기타 아시아제어\n740 영어\n750 독일어\n760 프랑스어\n770 스페인어 및 포르투갈어\n780 이탈리아어\n790 기타 제어\n"
        "800 문학\n810 한국문학\n820 중국문학\n830 일본문학 및 기타 아시아 제문학\n840 영미문학\n850 독일문학\n860 프랑스문학\n"
        "870 스페인문학 및 포르투갈문학\n880 이탈리아문학\n890 기타 제문학\n900 역사\n910 아시아\n920 유럽\n930 아프리카\n"
        "940 북아메리카\n950 남아메리카\n960 오세아니아 양극지방\n980 지리\n990 전기\n\n"
        "(보조) 문학 일의자리: -1 시 / -2 희곡 / -3 소설 / -4 수필·소품 / -5 연설·웅변 / -6 일기·서간·기행 / -7 풍자·유머 / -8 르포·기타\n"
        "예: 한국소설=813, 중국소설(홍콩 포함)=823, 일본소설=833, 영미소설=843\n"
        "(보조) 언어 일의자리: -1 음운·문자 / -2 어원 / -3 사전 / -4 어휘 / -5 문법 / -6 작문 / -7 독본·해석·회화 / -8 방언\n"
        "예: 한국어 문법=715, 중국어 회화=727, 영어회화=747\n"
    )
    
    hint_str = ", ".join(keywords_hint or [])
    user_prompt = (
        "아래 도서 정보(JSON)를 참고하여 **KDC 분류기호를 소수점 없이 3자리 정수로 한 줄**만 출력하라. "
        "만약 확실히 판단하기 어렵다면 **정확히 '직접분류추천'**만 출력하라.\n\n"
        f"※ 참고용 키워드 힌트(653): {hint_str or '(없음)'}\n"
        "이 힌트는 보조 신호일 뿐이며, 제목·목차·설명·카테고리 등의 원자료 및 KDC 규칙과 상충할 경우 무시해야 한다.\n\n"
        f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n\n"
        "출력 예시: 823 / 813 / 325 / 181 / (확신없음) 직접분류추천"
    )
    # 파서: 숫자(소수점 불허, 정수 3자리 고정) 또는 '직접분류추천' 인식
    def _parse_response(s: str) -> Optional[str]:
        if not s:
            return None
        s = s.strip()
        if "직접분류추천" in s:
            return "직접분류추천"
    # 첫 번째 1~3자리 연속 숫자만 추출 (뒤에 더 숫자 이어지면 무시)
        m = re.search(r"(?<!\d)(\d{1,3})(?!\d)", s)
        if not m:
            return None
        whole = m.group(1)
        num = whole.zfill(3)  # 항상 3자리로 보정: '5' -> '005', '81' -> '081'
    # 최종 검증: 딱 3자리 정수만 허용
        if not re.fullmatch(r"\d{3}", num):
            return None
        return num
        
    def _call_llm(sys_p: str, user_p: str, max_tokens: int) -> Optional[str]:
        resp = requests.post(
            OPENAI_CHAT_COMPLETIONS,
            headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
            json={
                "model": model,
                "messages": [
                    {"role": "system", "content": sys_p},
                    {"role": "user", "content": user_p},
                ],
                "temperature": 0.0,
                "max_tokens": max_tokens,
            },
            timeout=45,
        )
        resp.raise_for_status()
        data = resp.json()
        text = (data["choices"][0]["message"]["content"] or "").strip()
        # 1) 숫자 파싱
        code = _parse_response(text)
        if not code:
            return None
        # 2) 041 원작언어 기반 문학 계열 재정렬 (있을 경우만 적용)
        #    (BookInfo에 041 필드명이 다를 수 있어 안전하게 시도)
        marc041 = getattr(book, "marc041", "") or getattr(book, "field_041", "") or getattr(book, "f041", "")
        code = _rebase_8xx_with_language(code, marc041)
        # 3) 최종 반환
        return code
        
    # 1차: 메인 프롬프트
    try:
        code = _call_llm(sys_prompt, user_prompt, max_tokens=18)
        if code:
            return code
    except Exception as e:
        st.warning(f"1차 LLM 호출 경고: {e}")
    # 2차: 폴백(3자리 정수 또는 '직접분류추천')
    fb_sys = (
        "너는 KDC 제6판 기준 분류 사서다. "
        "가장 관련성이 높은 **3자리 정수**만 출력하라(예: 823, 325, 370). "
        "정확히 판단하기 어렵다면 **정확히 '직접분류추천'** 글자만 출력하라. "
        "다른 문자는 금지."
    )
    fb_user = f"도서 정보:\n{json.dumps(payload, ensure_ascii=False, indent=2)}"
    try:
        code = _call_llm(fb_sys, fb_user, max_tokens=8)
        if code:
            return code
    except Exception as e:
        st.error(f"2차 LLM 호출 오류: {e}")
    # 3차: 로컬 폴백 — 그래도 못 받으면 '직접분류추천'
    return "직접분류추천"

# ───────── 4) 파이프라인 ─────────
def get_kdc_from_isbn(isbn13: str, ttbkey: Optional[str], openai_key: str, model: str,
                      keywords_hint: list[str] | None = None) -> Optional[str]:
    info = aladin_lookup_by_api(isbn13, ttbkey) if ttbkey else None
    if not info:
        info = aladin_lookup_by_web(isbn13)
    if not info:
        st.warning("알라딘에서 도서 정보를 찾지 못했습니다.")
        return None
    code = ask_llm_for_kdc(info, api_key=openai_key, model=model, keywords_hint=keywords_hint)

    llm_meta = {
        "title": info.title,
        "author": info.author,
        "publisher": info.publisher,
        "pub_date": info.pub_date,
        "isbn13": info.isbn13,
        "category": info.category,
        "description": (info.description[:600] + "…") if info.description and len(info.description) > 600 else info.description,
        "toc": info.toc,
    }

    # 디버그용: 어떤 정보를 넘겼는지 보여주기(개인정보 없음) -> 상세메타로 옮김
    #with st.expander("LLM 입력 정보(확인용)"):
    #    st.json({
    #        "title": info.title,
    #        "author": info.author,
    #        "publisher": info.publisher,
    #        "pub_date": info.pub_date,
    #        "isbn13": info.isbn13,
    #        "category": info.category,
    #        "description": (info.description[:600] + "…") if info.description and len(info.description) > 600 else info.description,
    #        "toc": info.toc,
    #    })
    return code

# (김: 추가) mrc 파일 생성 (객체변환)
def mrk_str_to_field(line):
    # 0) None/빈 값
    if line is None:
        return None

    # 1) 이미 Field 유사 객체면 그대로 반환 (덕타이핑)
    try:
        if getattr(line, "tag", None) is not None and (hasattr(line, "data") or hasattr(line, "subfields")):
            return line
    except Exception:
        pass

    # 2) 문자열 확보 (아니면 str() 시도)
    if not isinstance(line, str):
        try:
            line = str(line)
        except Exception:
            return None
    
    s = line.strip()
    if not s.startswith("=") or len(s) < 8:
        return None

    # 3) 태그/인디케이터/본문 분해 (정규식으로 확정적으로 자르기)
    m = re.match(r"^=(\d{3})\s{2}(.)(.)(.*)$", s)
    if m:
        tag, ind1_raw, ind2_raw, tail = m.groups()
    else:
        # 컨트롤필드 (=008  <data>) 패턴
        m_ctl = re.match(r"^=(\d{3})\s\s(.*)$", s)
        if not m_ctl:
            return None
        tag, data = m_ctl.group(1), m_ctl.group(2).strip()
        if tag.isdigit() and int(tag) < 10:
            return Field(tag=tag, data=data) if data else None
        return None

    # 4) 컨트롤필드
    if tag.isdigit() and int(tag) < 10:
        data = (ind1_raw + ind2_raw + tail).strip()
        return Field(tag=tag, data=data) if data else None

    # 5) 데이터필드: 인디케이터 역슬래시(\) → 공백
    ind1 = " " if ind1_raw == "\\" else ind1_raw
    ind2 = " " if ind2_raw == "\\" else ind2_raw

    subs_part = tail or ""
    if "$" not in subs_part:
        return None  # 서브필드 없으면 의미없음

    # 6) 서브필드 파싱 ($a...$b...$I... 대소문자 코드 모두 허용)
    subfields = []
    i, L = 0, len(subs_part)
    while i < L:
        if subs_part[i] != "$":
            i += 1
            continue
        if i + 1 >= L:
            break
        code = subs_part[i + 1]
        j = i + 2
        while j < L and subs_part[j] != "$":
            j += 1
        value = subs_part[i + 2:j].strip()
        if code and value:
            subfields.append(Subfield(code, value))
        i = j

    if not subfields:
        return None

    return Field(tag=tag, indicators=[ind1, ind2], subfields=subfields)

def build_490_830_mrk_from_item(item):
    """
    알라딘 item에서 총서명/권호를 추출해
    MRK 문자열 형태의 490/830을 반환한다.
    (요구사항: 권호는 $v 없이 공백으로만 연결, 490 10 / 830 \0)
    """
    si = None
    if isinstance(item, dict):
        si = item.get("seriesInfo") or (item.get("subInfo") or {}).get("seriesInfo")

    cand = []
    if isinstance(si, list):
        cand = si
    elif isinstance(si, dict):
        cand = [si]

    series_name, series_vol = "", ""
    for ent in cand or []:
        if not isinstance(ent, dict):
            continue
        name = (ent.get("seriesName") or ent.get("name") or "").strip()
        vol  = (ent.get("volume") or ent.get("vol") or "").strip()
        if name:
            series_name, series_vol = name, vol
            break

    # 혹시 상위에 직접 박혀있는 케이스
    if not series_name:
        series_name = (item.get("seriesName") or "").strip()
    if not series_vol:
        series_vol = (item.get("volume") or "").strip()

    if not series_name:
        return "", ""   # 총서 없음

    series_display = f"{series_name} {series_vol}".strip()
    tag_490 = f"=490  10$a{series_display}"
    tag_830 = f"=830  \\0$a{series_display}"   # ← \0는 문자열에서 \\0로 이스케이프

    return tag_490, tag_830

# =========================
# --- 알라딘 상세 페이지 파싱 (형태사항) ---
# =========================
def detect_illustrations(text: str):
    if not text:
        return False, None

    keyword_groups = {
        "천연색삽화": ["삽화", "일러스트", "일러스트레이션", "illustration", "그림"],
        "삽화": ["흑백 삽화", "흑백 일러스트", "흑백 일러스트레이션", "흑백 그림"],
        "사진": ["사진", "포토", "photo", "화보"],
        "도표": ["도표", "차트", "그래프"],
        "지도": ["지도", "지도책"],
    }

    found_labels = set()

    for label, keywords in keyword_groups.items():
        if any(kw in text for kw in keywords):
            found_labels.add(label)

    if found_labels:
        return True, ", ".join(sorted(found_labels))
    else:
        return False, None

def parse_aladin_physical_book_info(html):
    """
    알라딘 상세 페이지 HTML에서 300 필드 파싱
    """
    soup = BeautifulSoup(html, "html.parser")

    # -------------------------------
    # 제목, 부제, 책소개
    # -------------------------------
    title = soup.select_one("span.Ere_bo_title")
    subtitle = soup.select_one("span.Ere_sub1_title")
    title_text = title.get_text(strip=True) if title else ""
    subtitle_text = subtitle.get_text(strip=True) if subtitle else ""

    description = None
    desc_tag = soup.select_one("div.Ere_prod_mconts_R")
    if desc_tag:
        description = desc_tag.get_text(" ", strip=True)

    # -------------------------------
    # 형태사항
    # -------------------------------
    form_wrap = soup.select_one("div.conts_info_list1")
    a_part = ""
    b_part = ""
    c_part = ""
    page_value = None
    size_value = None

    if form_wrap:
        form_items = [item.strip() for item in form_wrap.stripped_strings if item.strip()]
        for item in form_items:
            if re.search(r"(쪽|p)\s*$", item):
                page_match = re.search(r"\d+", item)
                if page_match:
                    page_value = int(page_match.group())
                    a_part = f"{page_match.group()} p."
            elif "mm" in item:
                size_match = re.search(r"(\d+)\s*[\*x×X]\s*(\d+)", item)
                if size_match:
                    width = int(size_match.group(1))
                    height = int(size_match.group(2))
                    size_value = f"{width}x{height}mm"
                    if width == height or width > height or width < height / 2:
                        w_cm = math.ceil(width / 10)
                        h_cm = math.ceil(height / 10)
                        c_part = f"{w_cm}x{h_cm} cm"
                    else:
                        h_cm = math.ceil(height / 10)
                        c_part = f"{h_cm} cm"

    # -------------------------------
    # 삽화 감지 (제목 + 부제 + 책소개 전체)
    # -------------------------------
    combined_text = " ".join(filter(None, [title_text, subtitle_text, description]))
    has_illus, illus_label = detect_illustrations(combined_text)
    if has_illus:
        b_part = illus_label

    # -------------------------------
    # 300 필드 조합
    # -------------------------------
    subfields_300 = []

    # 네가 위에서 채운 값들 그대로 사용
    # a_part = "528 p." 이런 식
    # b_part = "삽화"
    # c_part = "19cm" (또는 "19 cm", 등등)
    a_chunk = a_part if a_part else None
    b_chunk = b_part if b_part else None
    c_chunk = c_part if c_part else None

    # pymarc용 subfields 먼저 구성
    if a_chunk:
        subfields_300.append(Subfield("a", a_chunk))
    if b_chunk:
        subfields_300.append(Subfield("b", b_chunk))
    if c_chunk:
        subfields_300.append(Subfield("c", c_chunk))

    # 사람이 볼 MRK 한 줄 구성
    mrk_parts = []

    # 1) $a와 $b (":" 규칙)
    if a_chunk:
        # $a528 p.
        part_a = f"$a{a_chunk}"

        # b가 있으면 " :$b삽화"까지 붙여서 한 덩어리로
        if b_chunk:
            part_a += f" :$b{b_chunk}"

        mrk_parts.append(part_a)

    elif b_chunk:
        # a가 없고 b만 있는 특수 케이스
        mrk_parts.append(f"$b{b_chunk}")

    # 2) $c ("; $c" 규칙)
    if c_chunk:
        if mrk_parts:
            # 앞에 뭔가(a나 b)가 이미 있다면 ; $c 로 이어붙여
            mrk_parts.append(f"; $c{c_chunk}")
        else:
            # 아무 것도 없고 c만 있다면 그냥 $c부터 시작
            mrk_parts.append(f"$c{c_chunk}")

    # 3) 아무 정보도 못 뽑았으면 fallback
    if not mrk_parts:
        mrk_parts = ["$a1책."]
        subfields_300 = [Subfield("a", "1책.")]

    # =300  \\ + 조합
    field_300 = "=300  \\\\" + " ".join(mrk_parts)

    return {
        "300": field_300,
        "300_subfields": subfields_300,
        "page_value": page_value,
        "size_value": size_value,
        "illustration_possibility": illus_label if illus_label else "없음"
    }


def search_aladin_detail_page(link):
    try:
        res = requests.get(link, timeout=15)
        res.raise_for_status()
        return parse_aladin_physical_book_info(res.text), None
    except Exception as e:
        return {
            "300": "=300  \\$a1책. [상세 페이지 파싱 오류]",
            "300_subfields": [Subfield("a", "1책 [파싱 실패]")],
            "page_value": None,
            "size_value": None,
            "illustration_possibility": "정보 없음"
        }, f"Aladin 상세 페이지 크롤링 예외: {e}"
        
def build_300_from_aladin_detail(item: dict) -> tuple[str, Field]:
    """
    알라딘 상세 페이지 기반 300 필드를 생성한다.
    반환: (mrk 문자열, pymarc.Field 객체)
    """
    try:
        aladin_link = (item or {}).get("link", "")
        if not aladin_link:
            fallback_mrk = "=300  \\\\$a1책."
            dbg_err("[300] 알라딘 링크 없음 → 기본값 사용")
            return fallback_mrk, Field(
                tag="300",
                indicators=["\\", "\\"],
                subfields=[Subfield("a", "1책.")]
            )

        # 🔹 1) HTML 파싱 + MRK 문자열 + Subfield 리스트 생성
        detail_result, err = search_aladin_detail_page(aladin_link)

        # 🔹 2) MRK 문자열 (= 사람이 보는 예쁜 버전)
        tag_300 = detail_result.get("300") or "=300  \\\\$a1책."

        # 🔹 3) Subfield 리스트 (= 기계용 데이터 구조)
        subfields_300 = detail_result.get("300_subfields") or [Subfield("a", "1책.")]

        # 🔹 4) 여기서 Field 객체를 직접 생성한다 (mrk_str_to_field() ❌)
    
        f_300 = Field(
            tag="300",
            indicators=[" ", " "],
            subfields=subfields_300
        )

        if err:
            dbg_err(f"[300] {err}")
        dbg(f"[300] {tag_300}")

        # 삽화 감지 로그
        illus = detail_result.get("illustration_possibility")
        if illus and illus != "없음":
            dbg(f"[300] 삽화 감지됨 → {illus}")

        # 🔹 5) (사람이 보는 문자열, pymarc.Field) 둘 다 반환
        return tag_300, f_300

    except Exception as e:
        dbg_err(f"[300] 생성 중 예외: {e}")
        fallback_mrk = "=300  \\\\$a1책. [예외]"
        return fallback_mrk, Field(
            tag="300",
            indicators=["\\", "\\"],
            subfields=[Subfield("a", "1책. [예외]")]
        )

def build_300_mrk(item: dict) -> str:
    tag_300, _ = build_300_from_aladin_detail(item)
    if not tag_300:
        tag_300 = "=300  \\$a1책."
    return tag_300
# =========================================================================================

def generate_all_oneclick(isbn: str, reg_mark: str = "", reg_no: str = "", copy_symbol: str = "", use_ai_940: bool = True):
    mb = MarcBuilder()       # ✅ 단일 소스(Record+MRK)
    marc_rec = Record(to_unicode=True, force_utf8=True)
    meta = {"sources": {}, "notes": [], "provenance": {}}
    llm_input_info = None

    
    global CURRENT_DEBUG_LINES
    CURRENT_DEBUG_LINES = []

    pieces = []
    
    author_raw, _ = fetch_nlk_author_only(isbn)
    aladin = fetch_aladin_data(isbn)
    item = (aladin or {}).get("api") or {}
    detail = (aladin or {}).get("detail") or {}


    # ① 041/546 (네 최종 get_kormarc_tags 사용)
    tag_041_text = tag_546_text = _orig = None
    try:
        # ✅ isbn 말고 item, detail 넘기기
        res = get_kormarc_tags(item, detail)
        if isinstance(res, (list, tuple)) and len(res) == 3:
            tag_041_text, tag_546_text, _orig = res
        if isinstance(tag_041_text, str) and tag_041_text.startswith("📕 예외 발생"):
            tag_041_text = None
        if isinstance(tag_546_text, str) and tag_546_text.startswith("📕 예외 발생"):
            tag_546_text = None
    except Exception:
        tag_041_text = None
        tag_546_text = None
    origin_lang = None
    if tag_041_text:
        m = re.search(r"\$h([a-z]{3})", tag_041_text, re.IGNORECASE)
        if m:
            origin_lang = m.group(1).lower()

    # 245 / 246 / 700
    marc245 = build_245_with_people_from_sources(item, author_raw, prefer="aladin")
    f_245 = mrk_str_to_field(marc245)
    marc246 = build_246_from_aladin_item(item)
    f_246 = mrk_str_to_field(marc246)
    mrk_700 = build_700_people_pref_aladin(
        author_raw,
        item,
        origin_lang_code=origin_lang
    ) or []

        # 90010: JSON-LD + Wikidata(공저자 보충)
        # 90010: JSON-LD가 있으면 그걸 쓰고, 없으면 Wikidata/LOD로 폴백
    mrk_90010: list[str] = []

    # ✅ 0411($h) 있을 때만 90010 고려
    if origin_lang:
        original_author = (detail.get("original_author") or "").strip()

        if original_author and not re.search(r"[가-힣]", original_author):
            val = reorder_name_for_90010(original_author)
            mrk_90010.append(f"=900  10$a{val}")
        else:
            people = extract_people_from_aladin(item) if item else {}
            mrk_90010 = build_90010_from_wikidata(people, include_translator=False)
    else:
        dbg("90010: 0411($h) 없음 → 생성 생략")



    # 940: 245 $a만으로 생성, $n 있으면 숫자 읽기 금지
    a_out, n = parse_245_a_n(marc245)
    mrk_940 = build_940_from_title_a(a_out, use_ai=use_ai_940, disable_number_reading=bool(n))

    
    # 260 발행사항
    publisher_raw = (item or {}).get("publisher", "")          
    pubdate       = (item or {}).get("pubDate", "") or ""      
    pubyear       = (pubdate[:4] if len(pubdate) >= 4 else "") 

    bundle = build_pub_location_bundle(isbn, publisher_raw)     
    dbg(
        "📍[BUNDLE]",
        f"source={bundle.get('source')}",
        f"place_raw={bundle.get('place_raw')}",
        f"place_display={bundle.get('place_display')}",
        f"country_code={bundle.get('country_code')}",
    )
    for m in (bundle.get("debug") or []):
        dbg("[BUNDLE]", m)

    tag_260 = build_260(                                      
        place_display=bundle["place_display"],
        publisher_name=publisher_raw,
        pubyear=pubyear,
    )
    f_260 = mrk_str_to_field(tag_260)

     # ② 008 (041의 $a로 lang3 override)
    title   = (item or {}).get("title","") or ""
    category= (item or {}).get("categoryName","") or ""
    desc    = (item or {}).get("description","") or ""
    toc     = ((item or {}).get("subInfo",{}) or {}).get("toc","") or ""
    lang3_override = _lang3_from_tag041(tag_041_text) if tag_041_text else None
    
    data_008 = build_008_from_isbn(
        isbn,
        aladin_pubdate=(item or {}).get("pubDate","") or "",
        aladin_title=(item or {}).get("title","") or "",
        aladin_category=(item or {}).get("categoryName","") or "",
        aladin_desc=(item or {}).get("description","") or "",
        aladin_toc=((item or {}).get("subInfo",{}) or {}).get("toc","") or "",
        override_country3=bundle["country_code"],   # ✅ KPIPA DB 기반 country3
        override_lang3=lang3_override,
        cataloging_src="a",
    )
    field_008 = Field(tag='008', data=data_008)
    mb.add_ctl("008", data_008)

    # ③ 007 (물리적 자료 형태)
    field_007 = Field(tag='007', data='ta')
    pieces.append((field_007, "=007  ta"))
    

    # ③ 020 (가격 + NLK 부가기호) + 0201 set_isbn
    tag_020 = _build_020_from_item_and_nlk(isbn, item)
    f_020 = mrk_str_to_field(tag_020)
    nlk_extra = fetch_additional_code_from_nlk(isbn)
    set_isbn = nlk_extra.get("set_isbn", "").strip()

    # ④ 653 (GPT) — 먼저 생성하여 056에 힌트로 사용
    tag_653 = _build_653_via_gpt(item)
    f_653   = mrk_str_to_field(tag_653) if tag_653 else None

    # (내성 확보 + 재현성) 653 → 힌트 추출
    def _normalize_kw_hint(arr: list[str]) -> list[str]:
        seen = set(); out = []
        for w in (arr or []):
            w = (w or "").strip()
            if w and w not in seen:
                seen.add(w); out.append(w)
        # 사전순 정렬로 입력 순서 잡음 제거 + 최대 7개 제한
        return sorted(out)[:7]

    try:
        kw_hint_raw = _parse_653_keywords(tag_653) if tag_653 else []
        kw_hint = _normalize_kw_hint(kw_hint_raw)
    except Exception as e:
        dbg_err(f"653 파싱 실패: {e}")
        kw_hint = []

    dbg("653 keywords hint →", kw_hint)

    # ★ 056 (KDC) — 알라딘/스크레이핑 + LLM로 숫자만 받아 생성 (653 힌트 주입)
    kdc_code = None
    try:
        kdc_code = get_kdc_from_isbn(
            isbn,
            ttbkey=ALADIN_TTB_KEY,
            openai_key=openai_key,
            model=model,
            keywords_hint=kw_hint      # <= 새 인자 전달
        )
        # 숫자 포맷 검증(안전)
        if kdc_code and not re.fullmatch(r"\d{1,3}", kdc_code):
            kdc_code = None
    except Exception as e:
        dbg_err(f"056 생성 중 예외: {e}")

    # $2는 사용하는 판으로 (예: KDC6)
    tag_056 = f"=056  \\\\$a{kdc_code}$26" if kdc_code else None
    f_056 = mrk_str_to_field(tag_056)

    # 490.830 (총서)
    tag_490, tag_830 = build_490_830_mrk_from_item(item)
    f_490 = mrk_str_to_field(tag_490)
    f_830 = mrk_str_to_field(tag_830)

    # ③ 300 (형태사항)
    tag_300, f_300 = build_300_from_aladin_detail(item)

    
    # 950 (가격만 따로 생성)
    tag_950 = build_950_from_item_and_price(item, isbn)
    f_950 = mrk_str_to_field(tag_950)
    
    # 049
    field_049 = build_049(reg_mark, reg_no, copy_symbol)
    f_049 = mrk_str_to_field(field_049)    



    # =====================
    # 순서대로 조립 (MRK 출력 순서 유지)
    # ====================
    pieces.append((field_008, "=008  " + data_008))
    if f_020: pieces.append((f_020, tag_020))
    if set_isbn:
        tag_020_1 = f"=020  1\\$a{set_isbn} (set)"
        f_020_1 = mrk_str_to_field(tag_020_1)
        pieces.append((f_020_1, tag_020_1))
    is_translation = bool(tag_041_text and "$h" in tag_041_text)

    if is_translation:
        # 041
        f_041 = mrk_str_to_field(_as_mrk_041(tag_041_text))
        if f_041:
            pieces.append((f_041, _as_mrk_041(tag_041_text)))
    if f_056: pieces.append((f_056, tag_056))
    if f_245: pieces.append((f_245, marc245))
    if f_246: pieces.append((f_246, marc246))
    if f_260: pieces.append((f_260, tag_260))
    if f_300: pieces.append((f_300, tag_300))
    if f_490: pieces.append((f_490, tag_490))
    if tag_546_text:
        f_546 = mrk_str_to_field(_as_mrk_546(tag_546_text))
        if f_546:
            pieces.append((f_546, _as_mrk_546(tag_546_text)))
    if f_653: pieces.append((f_653, tag_653))
    for m in mrk_700:
        f = mrk_str_to_field(m)
        if not f:
            dbg_err(f"[mrk_str_to_field FAIL] {m}")
        else:
            pieces.append((f, m))
    for m in mrk_90010:
        f = mrk_str_to_field(m)
        if f: pieces.append((f, m))
    for m in mrk_940:
        f = mrk_str_to_field(m)
        if f: pieces.append((f, m))
    if f_830: pieces.append((f_830, tag_830))
    if f_950: pieces.append((f_950, tag_950))
    if f_049: pieces.append((f_049, field_049))

    mrk_strings = [m for f, m in pieces]

    mrk_text = "\n".join(mrk_strings)

    print("===== FINAL MRK TEXT DUMP =====")
    print(mrk_text)

        
    # Record 객체 생성
    for f, _ in pieces:
        marc_rec.add_field(f)

    # 메타정보
    meta = {
        "TitleA": a_out,
        "has_n": bool(n),
        "700_count": sum(1 for x in mrk_strings if x.startswith("=700")),
        "90010_count": sum(1 for x in mrk_strings if x.startswith("=90010")),
        "940_count": len(mrk_940),
        "Candidates": get_candidate_names_for_isbn(isbn),
        "041": tag_041_text,
        "546": tag_546_text,
        "020": tag_020,
        "056": tag_056,
        "653": tag_653,
        "kdc_code": kdc_code,
        "price_for_950": _extract_price_kr(item, isbn),
        "Publisher_raw": publisher_raw,
        "pubyear": pubyear,
        "Place_display": bundle.get("place_display"),
        "CountryCode_008": bundle.get("country_code"),
        "Publisher_resolved": bundle.get("resolved_publisher"),
        "Bundle_source": bundle.get("source"),
        "debug_lines": list(CURRENT_DEBUG_LINES),
        "Provenance": {"90010": LAST_PROV_90010},
    }
    meta["llm_input_info"] = llm_input_info

    marc_bytes = marc_rec.as_marc()       # MRC 파일용 (바이너리)
    
    
    print("TAGS:", [f.tag for f in marc_rec.get_fields()])
    print("MRK HEAD:\n", "\n".join(record_to_mrk_from_record(marc_rec).splitlines()[:10]))
    print("[DEBUG] tag_300 =", tag_300)
    print("[DEBUG] f_300 =", f_300)

    
    return marc_rec, marc_bytes, mrk_text, meta

def run_and_export(
    isbn: str,
    *,
    reg_mark: str = "",
    reg_no: str = "",
    copy_symbol: str = "",
    use_ai_940: bool = True,
    save_dir: str = "./output",
    preview_in_streamlit: bool = True,
):
    """
    네가 쓰는 기존 '원클릭 생성' 함수를 그대로 감싸서
    - Record → .mrc 바이트 만들고
    - MRK 텍스트 만들고
    - 디스크에 둘 다 저장하고
    - (선택) Streamlit 다운로드 버튼을 노출한다.
    """
    record, marc_bytes, mrk_text, meta = generate_all_oneclick(
        isbn,
        reg_mark=reg_mark,
        reg_no=reg_no,
        copy_symbol=copy_symbol,
        use_ai_940=use_ai_940,
    )

    save_marc_files(record, save_dir, isbn)

    if preview_in_streamlit:
        try:
            st.success("📦 MRC/MRK 파일이 저장되었습니다.")
            with st.expander("MRK 미리보기", expanded=True):
                st.text_area("MRK", mrk_text, height=320)
            st.download_button("📘 MARC (mrc) 다운로드", data=marc_bytes,
                               file_name=f"{isbn}.mrc", mime="application/marc")
            st.download_button("🧾 MARC (mrk) 다운로드", data=mrk_text,
                               file_name=f"{isbn}.mrk", mime="text/plain")
        except Exception:
            pass

    return record, marc_bytes, mrk_text, meta


# ========== MRC/MRK Export Helpers ==========
def record_to_mrk_from_record(rec: Record) -> str:
    lines = []
    # LDR
    leader = rec.leader.decode("utf-8") if isinstance(rec.leader, (bytes, bytearray)) else str(rec.leader)
    lines.append("=LDR  " + leader)

    for f in rec.get_fields():
        tag = f.tag
        # 컨트롤필드
        if tag.isdigit() and int(tag) < 10:
            lines.append(f"={tag}  " + (f.data or ""))
            continue

        # 데이터필드
        ind1 = (f.indicators[0] if getattr(f, "indicators", None) else " ") or " "
        ind2 = (f.indicators[1] if getattr(f, "indicators", None) else " ") or " "
        # 화면 표시용으론 공백→'\'로 보이게
        ind1_disp = "\\" if ind1 == " " else ind1
        ind2_disp = "\\" if ind2 == " " else ind2

        parts = ""
        subs = getattr(f, "subfields", None)

        # 신형: Subfield 객체 리스트
        if isinstance(subs, list) and subs and isinstance(subs[0], Subfield):
            for s in subs:
                parts += f"${s.code}{s.value}"

        # 구형: [code, value, code, value, ...]
        elif isinstance(subs, list):
            it = iter(subs)
            for code, val in zip(it, it):
                parts += f"${code}{val}"

        # 혹시 모를 폴백
        else:
            try:
                for s in f:
                    parts += f"${s.code}{s.value}"
            except Exception:
                pass

        lines.append(f"={tag}  {ind1_disp}{ind2_disp}{parts}")

    return "\n".join(lines)

def save_marc_files(record: Record, save_dir: str, base_filename: str) -> tuple[str, str]:
    """
    .mrc(바이너리)와 .mrk(텍스트)를 모두 저장하고 경로를 반환
    """
    import os
    os.makedirs(save_dir, exist_ok=True)

    mrc_path = os.path.join(save_dir, f"{base_filename}.mrc")
    with open(mrc_path, "wb") as f:
        f.write(record.as_marc())
        

    mrk_path = os.path.join(save_dir, f"{base_filename}.mrk")
    try:
        # MarcBuilder가 있으면 그쪽 텍스트를 쓰는 게 더 보기 좋음
        mrk_text = record_to_mrk_from_record(record)
    except Exception:
        mrk_text = record_to_mrk_from_record(record)

    with open(mrk_path, "w", encoding="utf-8") as f:
        f.write(mrk_text)

    return mrc_path, mrk_path


# =========================
# 🎛️ Streamlit UI
# =========================

st.header("📚 ISBN → MARC (일괄 처리 지원)")
st.checkbox("🧠 940 생성에 OpenAI 활용", value=True, key="use_ai_940")

# ✅ 폼: 입력 위젯 + 제출 트리거
with st.form(key="isbn_form", clear_on_submit=False):
    st.text_input(
        "🔹 단일 ISBN",
        placeholder="예: 9788937462849",
        key="single_isbn_input"
    )
    st.file_uploader(
        "📁 CSV 업로드 (UTF-8, 열: ISBN, 등록기호, 등록번호, 별치기호)",
        type=["csv"],
        key="csv_uploader"
    )

    # ✅ Enter 입력 시에도 이 버튼이 자동 눌림
    submitted = st.form_submit_button("🚀 변환 실행", use_container_width=True)

# ✅ 제출 후 처리 (폼 바깥)
if submitted:
    # 세션 값 읽기
    single_isbn = (st.session_state.get("single_isbn_input") or "").strip()
    uploaded = st.session_state.get("csv_uploader")

    # jobs 만들기
    jobs = []
    if single_isbn:
        jobs.append([single_isbn, "", "", ""])

    if uploaded is not None:
        try:
            df = load_uploaded_csv(uploaded)
            need_cols = {"ISBN", "등록기호", "등록번호", "별치기호"}
            if not need_cols.issubset(df.columns):
                st.error("❌ 필요한 열이 없습니다: ISBN, 등록기호, 등록번호, 별치기호")
                st.stop()
            rows = df[["ISBN", "등록기호", "등록번호", "별치기호"]].dropna(subset=["ISBN"]).copy()
            rows["별치기호"] = rows["별치기호"].fillna("")
            jobs.extend(rows.values.tolist())
        except Exception as e:
            st.error(f"❌ CSV 읽기 실패: {e}")
            st.stop()

    if not jobs:
        st.warning("변환할 항목이 없습니다. ISBN을 입력하거나 CSV를 업로드 해주세요.")
        st.stop()

    # ✅ 변환 실행 버튼 클릭 
    st.write(f"총 {len(jobs)}건 처리 중…")
    prog = st.progress(0)

    marc_all: list[str] = []
    st.session_state.meta_all = {}
    results: list[tuple[Record, str, str, dict]] = []

    for i, (isbn, reg_mark, reg_no, copy_symbol) in enumerate(jobs, start=1):
        record, marc_bytes, mrk_text, meta = run_and_export(
        isbn,
        reg_mark=reg_mark,
        reg_no=reg_no,
        copy_symbol=copy_symbol,
        use_ai_940=True,
        save_dir="./output",
        preview_in_streamlit=True,
    )

    # 결과 카드
    with st.container():
        #st.subheader(f"📘 ISBN: {isbn}") // run_and_export와 겹쳐서 주석처리

        # --- MRK 미리보기 ---
        #st.markdown("#### 📄 MRK 미리보기")
        #st.code(mrk_text or "(MRK 생성 실패)", language="text")

        # --- 메타 정보 + 디버그는 EXPANDER 안으로 ---
        with st.expander("🧭 상세 메타 · 디버그 보기"):
            # top summary
            cand = ", ".join(meta.get("Candidates", [])) if meta else ""
            c700 = meta.get("700_count", None)
            c90010 = meta.get("90010_count", 0)
            c940 = meta.get("940_count", 0)

            st.write(f"**후보저자**: {cand}")
            st.write(f"**700 필드 수**: {c700 if c700 is not None else '—'}")
            st.write(f"**90010 필드 수**: {c90010}")
            st.write(f"**940 필드 수**: {c940}")
            st.write(f"**MRK 길이**: {len(mrk_text)}")

            # meta JSON
            if meta:
                safe_meta = {k: v for k, v in meta.items() if k != 'debug_lines'}
                st.json(safe_meta)
            
            if meta and meta.get("llm_input_info"):
                st.subheader("LLM 입력 정보(확인용)")
                st.json(meta["llm_input_info"])

            # debug lines
            dbg_lines = meta.get("debug_lines") or []
            if dbg_lines:
                st.subheader("Debug Lines")
                st.text("\n".join(str(x) for x in dbg_lines))
            else:
                st.caption("표시할 디버그 로그가 없습니다.")

    # 프로그레스바 업데이트
    prog.progress(i / len(jobs))

with st.expander("⚙️ 사용 팁"):
    st.markdown(
        """
- 008: 일단 확인 
- 청구기호: 분류기호는 참고만! 코라스에서 청구기호 생성 누르기
- 서명: 권차기호와 권차명을 확인☆ 다양한 서명은 직접 확인★       
- 저자명: 7001로 태그가 생성되니 7000인지, 710인지 확인☆ 외국저자 이름이 성-이름 순이 맞는지 반드시 확인★
- 총서: 총서번호 확인★
        """
    )

