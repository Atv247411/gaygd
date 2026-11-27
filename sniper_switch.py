#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SNIPER SWITCH - công tắc TỪ XA của chủ tool: tắt / mở sniper.py trên MỌI máy đã giao.
Không cần chạy cùng lúc với tool chính, không cần cùng máy, không cần cùng mạng.

Cách hoạt động: tool này ký (Ed25519) một tệp trạng thái nhỏ {ON | OFF} rồi đăng lên một link công khai
(mặc định là một tệp trong repo GitHub của bạn). sniper.py (GATE_MODE = "remote") tải tệp đó định kỳ và chỉ
chạy khi trạng thái là ON. Khoá riêng chỉ nằm ở máy bạn nên khách không tự giả lệnh ON được.
Không cần cài thư viện nào (chỉ thư viện chuẩn của Python).

Cài một lần:
    python sniper_switch.py init --repo TÊN/REPO --patch sniper.py
      (repo GitHub phải công khai; token GitHub cần quyền ghi nội dung repo đó, nhập khi được hỏi hoặc đặt biến SNIPER_GH_TOKEN)
Dùng hằng ngày:
    python sniper_switch.py                      # menu: 1 = TẮT, 2 = MỞ, 3 = xem trạng thái
    python sniper_switch.py off --msg "Bảo trì"  # lời nhắn hiện trên màn hình khoá của khách
    python sniper_switch.py on
    python sniper_switch.py status
Sau khi `init --patch`, chép sniper.py đã vá cho khách (hoặc dùng nó làm bản gốc để `embed` token từng khách).

Cấu hình, khoá riêng và token GitHub nằm ở sniper_switch.json cạnh tool này, quyền 600 (đổi chỗ bằng biến SNIPER_SWITCH_HOME).
MẤT FILE NÀY là mất quyền điều khiển các bản đã giao: hãy sao lưu và đừng gửi cho ai.
"""
from __future__ import annotations

import argparse
import base64
import getpass
import hashlib
import json
import os
import re
import secrets
import shutil
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime
from pathlib import Path

HOME = Path(os.environ.get("SNIPER_SWITCH_HOME", str(Path(__file__).resolve().parent)))
CONFIG_PATH = HOME / "sniper_switch.json"
# Chỉ đổi để thử với server giả, bình thường đừng đặt.
API_BASE = os.environ.get("SNIPER_SWITCH_API_BASE", "https://api.github.com").rstrip("/")
HTTP_TIMEOUT = 20.0
READ_MAX = 16384        # đọc tối đa từng này byte khi tải tệp trạng thái về để kiểm tra
NOTE_MAX = 200          # phải khớp REMOTE_NOTE_MAX trong sniper.py
DOC_VERSION = 1         # phải khớp phiên bản tệp trạng thái mà sniper.py chấp nhận

ESC = "\x1b["
RESET = ESC + "0m"


def paint(text: str, fg: int, bold: bool = True) -> str:
    return "%s%s38;5;%dm%s%s" % (ESC, "1;" if bold else "", fg, text, RESET)


def badge(text: str, bg: int) -> str:
    return "%s1;38;5;16;48;5;%dm%s%s" % (ESC, bg, text, RESET)


class SwitchError(Exception):
    """Lỗi có thể nói thẳng cho chủ tool (sai cấu hình, token, mạng...)."""


# ============================================================================
#  Ed25519 (RFC 8032, mã tham chiếu). Chỉ thư viện chuẩn. Mã chung với sniper.py (bên đó chỉ có phần xác minh).
# ============================================================================
_P = 2 ** 255 - 19
_Q = 2 ** 252 + 27742317777372353535851937790883648493
_D = -121665 * pow(121666, _P - 2, _P) % _P
_SQRT_M1 = pow(2, (_P - 1) // 4, _P)


def _add(a, b):
    x = (a[1] - a[0]) * (b[1] - b[0]) % _P
    y = (a[1] + a[0]) * (b[1] + b[0]) % _P
    c = 2 * a[3] * b[3] * _D % _P
    d = 2 * a[2] * b[2] % _P
    e, f, g, h = y - x, d - c, d + c, y + x
    return (e * f % _P, g * h % _P, f * g % _P, e * h % _P)


def _mul(s, pt):
    acc = (0, 1, 1, 0)
    while s > 0:
        if s & 1:
            acc = _add(acc, pt)
        pt = _add(pt, pt)
        s >>= 1
    return acc


def _same(a, b):
    return (a[0] * b[2] - b[0] * a[2]) % _P == 0 and (a[1] * b[2] - b[1] * a[2]) % _P == 0


def _recover_x(y, sign):
    if y >= _P:
        return None
    x2 = (y * y - 1) * pow(_D * y * y + 1, _P - 2, _P) % _P
    if x2 == 0:
        return None if sign else 0
    x = pow(x2, (_P + 3) // 8, _P)
    if (x * x - x2) % _P:
        x = x * _SQRT_M1 % _P
    if (x * x - x2) % _P:
        return None
    if (x & 1) != sign:
        x = _P - x
    return x


def _compress(pt) -> bytes:
    zinv = pow(pt[2], _P - 2, _P)
    x, y = pt[0] * zinv % _P, pt[1] * zinv % _P
    return int.to_bytes(y | ((x & 1) << 255), 32, "little")


def _decompress(s: bytes):
    y = int.from_bytes(s, "little")
    sign = y >> 255
    y &= (1 << 255) - 1
    x = _recover_x(y, sign)
    return None if x is None else (x, y, 1, x * y % _P)


_GY = 4 * pow(5, _P - 2, _P) % _P
_GX = _recover_x(_GY, 0)
_G = (_GX, _GY, 1, _GX * _GY % _P)


def _h_modq(data: bytes) -> int:
    return int.from_bytes(hashlib.sha512(data).digest(), "little") % _Q


def _expand(seed: bytes):
    h = hashlib.sha512(seed).digest()
    a = int.from_bytes(h[:32], "little")
    a &= (1 << 254) - 8
    a |= 1 << 254
    return a, h[32:]


def public_from_seed(seed: bytes) -> bytes:
    return _compress(_mul(_expand(seed)[0], _G))


def sign(seed: bytes, msg: bytes) -> bytes:
    a, prefix = _expand(seed)
    pub = _compress(_mul(a, _G))
    r = _h_modq(prefix + msg)
    rs = _compress(_mul(r, _G))
    s = (r + _h_modq(rs + pub + msg) * a) % _Q
    return rs + int.to_bytes(s, 32, "little")


def verify(public: bytes, msg: bytes, sig: bytes) -> bool:
    if len(public) != 32 or len(sig) != 64:
        return False
    a, r = _decompress(public), _decompress(sig[:32])
    if a is None or r is None:
        return False
    s = int.from_bytes(sig[32:], "little")
    if s >= _Q:
        return False
    h = _h_modq(sig[:32] + public + msg)
    return _same(_mul(s, _G), _add(r, _mul(h, a)))


# ============================================================================
#  Tệp trạng thái
# ============================================================================
def clean_note(s: str) -> str:
    s = s.encode("utf-8", "ignore").decode("utf-8")          # bỏ ký tự surrogate lạ để ký/mã hoá không lỗi
    return "".join(ch for ch in s if ch.isprintable())[:NOTE_MAX]


def make_doc(seed: bytes, state: str, seq: int, note: str) -> bytes:
    """{"v":1,"payload":"<json>","sig":"<hex>"}: chữ ký tính trên đúng chuỗi payload nên không phải chuẩn hoá JSON."""
    payload = json.dumps({"state": state, "seq": seq, "issued": int(time.time()), "note": clean_note(note)},
                         ensure_ascii=False, separators=(",", ":"))
    sig = sign(seed, payload.encode("utf-8"))
    return (json.dumps({"v": DOC_VERSION, "payload": payload, "sig": sig.hex()}, ensure_ascii=False) + "\n").encode("utf-8")


def read_doc(raw: bytes | None, pub: bytes):
    """Trả payload (dict) nếu tệp đúng định dạng và chữ ký khớp khoá công khai `pub`; ngược lại None."""
    if not raw or len(raw) > READ_MAX:
        return None
    try:
        doc = json.loads(raw.decode("utf-8"))
        payload, sig = doc["payload"], bytes.fromhex(doc["sig"])
        if doc.get("v") != DOC_VERSION or not isinstance(payload, str) or not verify(pub, payload.encode("utf-8"), sig):
            return None
        p = json.loads(payload)
        ok = (p["state"] in ("on", "off") and type(p["seq"]) is int and p["seq"] >= 1
              and type(p["issued"]) is int and isinstance(p.get("note", ""), str))
    except (ValueError, KeyError, TypeError, AttributeError, UnicodeDecodeError, RecursionError):
        return None
    return {"state": p["state"], "seq": p["seq"], "issued": p["issued"], "note": p.get("note", "")} if ok else None


# ============================================================================
#  Cấu hình
# ============================================================================
def load_cfg() -> dict:
    try:
        text = CONFIG_PATH.read_text(encoding="utf-8")
    except FileNotFoundError:
        raise SwitchError("Chưa có cấu hình. Chạy:  python sniper_switch.py init --repo TÊN/REPO --patch sniper.py")
    except OSError as e:
        raise SwitchError("Không đọc được %s: %s" % (CONFIG_PATH, e))
    try:
        cfg = json.loads(text)
        seed, pub = bytes.fromhex(cfg["seed"]), bytes.fromhex(cfg["pub"])
        if len(seed) != 32 or public_from_seed(seed) != pub or cfg["backend"] not in ("github", "file"):
            raise ValueError
    except (ValueError, KeyError, TypeError):
        raise SwitchError("%s bị hỏng hoặc khoá riêng không khớp khoá công khai. Khôi phục từ bản sao lưu." % CONFIG_PATH)
    return cfg


def save_cfg(cfg: dict) -> None:
    HOME.mkdir(parents=True, exist_ok=True)
    tmp = CONFIG_PATH.with_suffix(".tmp")
    fd = os.open(str(tmp), os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)     # file chứa khoá riêng + token: tạo sẵn quyền 600
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    os.replace(tmp, CONFIG_PATH)


def public_url(cfg: dict) -> str:
    if cfg.get("public_url"):
        return cfg["public_url"]
    if cfg["backend"] == "github":
        return "https://raw.githubusercontent.com/%s/%s/%s" % (cfg["repo"], cfg["branch"], urllib.parse.quote(cfg["path"], safe="/"))
    return ""


# ============================================================================
#  Đăng trạng thái (backend: github | file)
# ============================================================================
def _gh(method: str, url: str, token: str, body=None):
    data = json.dumps(body).encode("utf-8") if body is not None else None
    headers = {"Authorization": "Bearer " + token, "Accept": "application/vnd.github+json",
               "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "sniper-switch"}
    if data is not None:
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as r:
            code, text = r.status, r.read(1 << 20)
    except urllib.error.HTTPError as e:
        code, text = e.code, e.read(1 << 20)
    except (urllib.error.URLError, OSError) as e:
        raise SwitchError("Lỗi mạng khi gọi GitHub: %s" % str(e)[:100])
    try:
        return code, json.loads(text.decode("utf-8") or "null")
    except (ValueError, UnicodeDecodeError):
        return code, None


def _gh_fail(code: int, j) -> SwitchError:
    msg = str(j.get("message", "")) if isinstance(j, dict) else ""
    if code == 401:
        return SwitchError("GitHub từ chối token (401): token sai hoặc hết hạn.")
    if code in (403, 404):
        return SwitchError("GitHub trả %d: repo/nhánh không tồn tại, hoặc token không có quyền ghi nội dung repo này. %s" % (code, msg[:100]))
    return SwitchError("GitHub trả HTTP %d: %s" % (code, msg[:120]))


def _contents_url(cfg: dict) -> str:
    return "%s/repos/%s/contents/%s" % (API_BASE, cfg["repo"], urllib.parse.quote(cfg["path"], safe="/"))


def read_current(cfg: dict):
    """Đọc tệp trạng thái hiện đang đăng ở nguồn gốc (qua API, không qua CDN). Trả (sha hoặc None, bytes hoặc None)."""
    if cfg["backend"] == "file":
        try:
            return None, Path(cfg["out"]).read_bytes()
        except OSError:
            return None, None
    code, j = _gh("GET", _contents_url(cfg) + "?ref=" + urllib.parse.quote(cfg["branch"], safe=""), cfg["token"])
    if code == 200 and isinstance(j, dict) and isinstance(j.get("sha"), str):
        try:
            return j["sha"], base64.b64decode(str(j.get("content", "")))
        except ValueError:
            return j["sha"], None
    if code == 404:
        return None, None            # chưa có tệp (hoặc GitHub giấu repo vì thiếu quyền: lúc ghi sẽ báo lỗi rõ hơn)
    raise _gh_fail(code, j)


def publish(cfg: dict, state: str, note: str) -> int:
    """Ký và đăng trạng thái mới. seq = max(seq đang đăng, seq lần trước) + 1 nên luôn tăng dù chạy từ máy nào. Trả về seq."""
    seed, pub = bytes.fromhex(cfg["seed"]), bytes.fromhex(cfg["pub"])
    for attempt in (1, 2):
        sha, cur = read_current(cfg)
        cur_doc = read_doc(cur, pub)
        seq = max(cur_doc["seq"] if cur_doc else 0, int(cfg.get("last_seq", 0))) + 1
        raw = make_doc(seed, state, seq, note)
        if cfg["backend"] == "file":
            out = Path(cfg["out"])
            tmp = out.with_name(out.name + ".tmp")
            try:
                tmp.write_bytes(raw)
                os.replace(tmp, out)
            except OSError as e:
                raise SwitchError("Không ghi được %s: %s" % (out, e))
        else:
            body = {"message": "state %s #%d" % (state, seq), "content": base64.b64encode(raw).decode("ascii"),
                    "branch": cfg["branch"]}
            if sha:
                body["sha"] = sha
            code, j = _gh("PUT", _contents_url(cfg), cfg["token"], body)
            if code in (409, 422) and attempt == 1:
                continue                 # sha lệch vì có người vừa sửa tệp: đọc lại và thử đúng 1 lần nữa
            if code not in (200, 201):
                raise _gh_fail(code, j)
        cfg["last_seq"] = seq
        save_cfg(cfg)
        return seq
    raise SwitchError("Không đăng được sau 2 lần thử (xung đột sha).")


def http_get(url: str):
    """Tải link công khai như khách làm. Trả (bytes, None) hoặc (None, lý do)."""
    req = urllib.request.Request(url, headers={"User-Agent": "sniper-switch", "Cache-Control": "no-cache"})
    try:
        with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as r:
            return r.read(READ_MAX), None
    except urllib.error.HTTPError as e:
        return None, "HTTP %d" % e.code
    except (urllib.error.URLError, OSError) as e:
        return None, str(e)[:80]


# ============================================================================
#  Hiển thị + lệnh
# ============================================================================
def when(ts: int) -> str:
    try:
        return datetime.fromtimestamp(ts).strftime("%d/%m %H:%M:%S")
    except (OverflowError, OSError, ValueError):
        return "?"


def describe(d) -> str:
    if d is None:
        return paint("chưa đăng / không đọc được", 214)
    on = d["state"] == "on"
    return "%s  seq %d, %s%s" % (badge(" BẬT " if on else " TẮT ", 46 if on else 196), d["seq"], when(d["issued"]),
                                 ('  "%s"' % d["note"]) if d["note"] else "")


def cmd_status(cfg: dict) -> None:
    pub = bytes.fromhex(cfg["pub"])
    _, raw = read_current(cfg)
    src = read_doc(raw, pub)
    print("Nguồn gốc  :", describe(src))
    url = public_url(cfg)
    if not url:
        print("Khách thấy : (chưa có link công khai trong cấu hình)")
        return
    raw2, err = http_get(url)
    if raw2 is None:
        print("Khách thấy : không tải được %s (%s)" % (url, err))
        return
    pubdoc = read_doc(raw2, pub)
    print("Khách thấy :", describe(pubdoc))
    if pubdoc is None:
        print("             tệp ở link công khai không hợp lệ với khoá này: kiểm tra repo có công khai không, đúng nhánh/đường dẫn không.")
    elif src and pubdoc["seq"] != src["seq"]:
        print("             link công khai còn bản cũ (bộ nhớ đệm của host): khách sẽ thấy bản mới sau ít phút.")
    print("Link       :", url)


def cmd_set(cfg: dict, state: str, note: str) -> None:
    seq = publish(cfg, state, note)
    print("Đã đăng %s (seq %d)%s." % ("TẮT" if state == "off" else "BẬT", seq, (' với lời nhắn "%s"' % clean_note(note)) if note else ""))
    print("Khách nhận trong vòng (chu kỳ tải của tool chính + bộ nhớ đệm của host). Xem lại bằng:  python sniper_switch.py status")


def patch_file(cfg: dict, path: str) -> None:
    """Điền REMOTE_URL và REMOTE_PUBKEY vào sniper.py (có bản sao lưu .bak-<giờ>)."""
    url = public_url(cfg)
    if not url:
        raise SwitchError("Cấu hình chưa có link công khai (public_url).")
    src = Path(path)
    try:
        text = src.read_text(encoding="utf-8")
    except OSError as e:
        raise SwitchError("Không đọc được %s: %s" % (src, e))
    out = text
    for name, value in (("REMOTE_URL", url), ("REMOTE_PUBKEY", cfg["pub"])):
        pat = re.compile(r'^(%s: str = )"[^"\n]*"' % name, re.M)
        if len(pat.findall(out)) != 1:
            raise SwitchError("%s không có đúng 1 dòng `%s: str = \"...\"` (đây có phải sniper.py bản có công tắc từ xa không?)" % (src, name))
        out = pat.sub(lambda m: m.group(1) + json.dumps(value), out, count=1)
    bak = src.with_name("%s.bak-%s" % (src.name, datetime.now().strftime("%Y%m%d%H%M%S")))
    try:
        shutil.copy2(str(src), str(bak))
        src.write_text(out, encoding="utf-8")
    except OSError as e:
        raise SwitchError("Không ghi được %s: %s" % (src, e))
    print("Đã vá %s (bản gốc lưu ở %s)." % (src, bak.name))


def cmd_init(a) -> None:
    if CONFIG_PATH.exists() and not a.force:
        raise SwitchError("Đã có %s. Init lại sẽ tạo khoá MỚI và mọi bản đã giao sẽ không còn điều khiển được. "
                          "Nếu thật sự muốn thì thêm --force." % CONFIG_PATH)
    cfg: dict = {"backend": a.backend, "last_seq": 0}
    if a.backend == "github":
        repo = a.repo or input("Repo GitHub (dạng TÊN/REPO, phải công khai) > ").strip()
        if not re.fullmatch(r"[A-Za-z0-9_.\-]+/[A-Za-z0-9_.\-]+", repo):
            raise SwitchError("Repo phải có dạng TÊN/REPO.")
        token = os.environ.get("SNIPER_GH_TOKEN") or getpass.getpass("Token GitHub (ẩn khi gõ) > ").strip()
        if not token:
            raise SwitchError("Chưa có token GitHub.")
        if not re.fullmatch(r"[A-Za-z0-9_.\-/]+", a.path) or ".." in a.path.split("/"):
            raise SwitchError("--path chỉ gồm chữ, số, _ . - / và không có '..'.")
        cfg.update(repo=repo, branch=a.branch, path=a.path, token=token)
        if a.url:
            cfg["public_url"] = a.url
    else:
        cfg.update(out=a.out or "state.json", public_url=a.url or input("Link công khai nơi bạn sẽ đưa tệp lên > ").strip())
        if not re.match(r"https?://", cfg["public_url"]):
            raise SwitchError("Link công khai phải bắt đầu bằng http:// hoặc https://")
    seed = secrets.token_bytes(32)
    cfg.update(seed=seed.hex(), pub=public_from_seed(seed).hex())
    save_cfg(cfg)                                    # lưu khoá trước khi đụng tới mạng để không bao giờ mất khoá đã sinh
    print("Đã tạo khoá và lưu ở %s (quyền 600)." % CONFIG_PATH)
    print("HÃY SAO LƯU file đó. Mất nó là mất quyền tắt/mở các bản đã giao.")
    print()
    print("Hai dòng này nằm trong sniper.py (đã tự điền nếu bạn dùng --patch):")
    print('    REMOTE_URL: str = %s' % json.dumps(public_url(cfg)))
    print('    REMOTE_PUBKEY: str = %s' % json.dumps(cfg["pub"]))
    if a.patch:
        patch_file(cfg, a.patch)
    try:
        seq = publish(cfg, "on", "")
    except SwitchError as e:
        print()
        print("Chưa đăng được trạng thái đầu tiên: %s" % e)
        print("Sửa repo/token trong %s rồi chạy:  python sniper_switch.py on" % CONFIG_PATH.name)
        print("Tới lúc đó mọi bản sniper.py đã vá sẽ bị khoá (chưa có tệp trạng thái).")
        return
    print()
    print("Đã đăng trạng thái BẬT đầu tiên (seq %d)." % seq)


def menu(cfg: dict) -> None:
    pub = bytes.fromhex(cfg["pub"])
    while True:
        try:
            _, raw = read_current(cfg)
            now = describe(read_doc(raw, pub))
        except SwitchError as e:
            now = paint("không đọc được: %s" % e, 214)
        print()
        print(paint("SNIPER SWITCH", 201) + paint("  công tắc từ xa", 245, False))
        print("Đang đăng :", now)
        print(badge(" 1 ", 196) + " TẮT tool trên mọi máy")
        print(badge(" 2 ", 46) + " MỞ tool")
        print(badge(" 3 ", 245) + " Xem trạng thái khách đang thấy")
        print(badge(" 0 ", 245) + " Thoát")
        try:
            c = input("Chọn > ").strip().lower()
            if c in ("1", "2"):
                note = input("Lời nhắn hiện cho khách (Enter = không có) > ")
                if c == "1" and input("TẮT tool trên MỌI máy đã giao? Gõ y để xác nhận > ").strip().lower() != "y":
                    print("Đã huỷ.")
                    continue
                cmd_set(cfg, "off" if c == "1" else "on", note)
            elif c == "3":
                cmd_status(cfg)
            elif c in ("0", "q"):
                return
        except SwitchError as e:
            print(paint("Lỗi: %s" % e, 196))
        except EOFError:
            return


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="sniper_switch", description="Công tắc từ xa tắt/mở sniper.py trên mọi máy đã giao.")
    sub = ap.add_subparsers(dest="cmd")
    i = sub.add_parser("init", help="tạo khoá + cấu hình, (tuỳ chọn) vá sniper.py, đăng trạng thái BẬT đầu tiên")
    i.add_argument("--backend", choices=("github", "file"), default="github")
    i.add_argument("--repo", help="github: TÊN/REPO (công khai)")
    i.add_argument("--branch", default="main", help="github: nhánh (mặc định main)")
    i.add_argument("--path", default="state.json", help="github: đường dẫn tệp trong repo (mặc định state.json)")
    i.add_argument("--out", help="file: nơi ghi tệp trạng thái (mặc định state.json); bạn tự đưa nó lên --url")
    i.add_argument("--url", help="link công khai tới tệp trạng thái (bắt buộc với backend file; github thì tự suy ra)")
    i.add_argument("--patch", metavar="SNIPER.PY", help="điền REMOTE_URL và REMOTE_PUBKEY vào file sniper.py này")
    i.add_argument("--force", action="store_true", help="cho phép ghi đè cấu hình cũ (tạo khoá mới!)")
    for name, text in (("on", "MỞ tool"), ("off", "TẮT tool")):
        p = sub.add_parser(name, help=text)
        p.add_argument("--msg", default="", help="lời nhắn hiện trên màn hình khoá của khách")
    sub.add_parser("status", help="xem trạng thái đang đăng và trạng thái khách đang thấy")
    pt = sub.add_parser("patch", help="điền REMOTE_URL và REMOTE_PUBKEY vào một file sniper.py")
    pt.add_argument("file")
    a = ap.parse_args(argv)
    try:
        if a.cmd == "init":
            cmd_init(a)
        elif a.cmd == "patch":
            patch_file(load_cfg(), a.file)
        elif a.cmd in ("on", "off"):
            cmd_set(load_cfg(), a.cmd, a.msg)
        elif a.cmd == "status":
            cmd_status(load_cfg())
        else:
            menu(load_cfg())
    except SwitchError as e:
        print("Lỗi: %s" % e, file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
