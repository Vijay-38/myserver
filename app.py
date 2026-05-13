import base64
import json
import os
import time
import uuid
import threading
import asyncio
import logging
import glob
import datetime
from pathlib import Path
from urllib.parse import urlparse, parse_qs

import jwt
import requests
import urllib.request
import urllib.error
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from flask import Flask, request, jsonify, send_from_directory, Response
from flask_compress import Compress
import psycopg2
from psycopg2 import Error as Psycopg2Error
from psycopg2.errors import IntegrityError as Psycopg2IntegrityError
from psycopg2.extras import RealDictCursor
import websockets

logging.basicConfig(level=logging.DEBUG)

try:
    from google.oauth2 import service_account as ga_service_account
    from google.auth.transport import requests as ga_requests
    GOOGLE_AUTH_AVAILABLE = True
except Exception:
    GOOGLE_AUTH_AVAILABLE = False

app = Flask(__name__)
Compress(app)

app.config['JWT_SECRET'] = os.environ.get('JWT_SECRET', 'change_this_secret')
app.config['JWT_ALGO'] = 'HS256'
app.config['JWT_EXP_SECONDS'] = 60 * 60 * 24 * 7
app.config['FCM_SERVICE_ACCOUNT'] = os.environ.get('FCM_SERVICE_ACCOUNT')
app.config['FCM_PROJECT_ID'] = os.environ.get('FCM_PROJECT_ID')
FCM_V1_URL_TEMPLATE = 'https://fcm.googleapis.com/v1/projects/{project_id}/messages:send'

_fcm_sa_credentials = None
_fcm_sa_token = None
_fcm_sa_token_expiry = 0

DB_CONFIG = {
    "host": os.environ.get("PG_HOST", "pg-3ed471db-chating-app.g.aivencloud.com"),
    "user": os.environ.get("PG_USER", "avnadmin"),
    "password": os.environ.get("PG_PASSWORD", "AVNS_JgoomW9hD_xAEXbxkeQ"),
    "database": os.environ.get("PG_DBNAME", "defaultdb"),
    "port": int(os.environ.get("PG_PORT", "21668")),
    "sslmode": "require",
    "connect_timeout": 10,
}

ALLOWED_EXTENSIONS = {
    'png', 'jpg', 'jpeg', 'gif', 'mp4', 'mov', 'webm', 'mkv', 'avi', 'flv',
    'pdf', 'doc', 'docx', 'xls', 'xlsx', 'ppt', 'pptx', 'txt', 'csv',
    'zip', 'rar', '7z', 'apk', 'svg', 'mp3', 'wav', 'ogg', 'm4a'
}

BASE_DIR = os.environ.get("BASE_DIR", os.path.join(os.getcwd(), "data"))
PROFILE_DIR = os.path.join(BASE_DIR, "profile")
STATUSES_DIR = os.path.join(BASE_DIR, "statuces")
THREATS_DIR = os.path.join(BASE_DIR, "threates")
UPLOADS_DIR = os.path.join(BASE_DIR, "uploads")

for dir_path in [PROFILE_DIR, STATUSES_DIR, THREATS_DIR, UPLOADS_DIR]:
    os.makedirs(dir_path, exist_ok=True)

app.config['MESSAGES_FOLDER'] = UPLOADS_DIR

ALLOWED_ORIGINS = {
    "http://localhost:5173",
    "https://chatupsignin.netlify.app",
    "http://localhost:5174",
    "http://localhost:5175",
    "http://localhost:5176",
    "http://localhost:5177",
    "https://localhost",
}

@app.after_request
def add_cors_headers(response):
    origin = request.headers.get("Origin")
    if origin in ALLOWED_ORIGINS:
        response.headers["Access-Control-Allow-Origin"] = origin
    response.headers["Access-Control-Allow-Headers"] = "Content-Type, Authorization"
    response.headers["Access-Control-Allow-Methods"] = "GET, POST, PUT, DELETE, OPTIONS"
    response.headers["Access-Control-Allow-Credentials"] = "true"
    return response

@app.route("/", methods=["OPTIONS"])
def handle_options():
    return "", 204

_authed_route_cache = {}
_rate_limit_store = {}

connected_clients = {}
connected_lock = threading.Lock()
ws_loop = None

WEBRTC_MESSAGES = {}
WEBRTC_ACKS = {}
WEBRTC_SIGNALS = {}
WEBRTC_ONLINE = {}
WEBRTC_LOCK = threading.Lock()

SSE_CLIENTS = {}
SSE_CLIENT_COUNTER = 0
SSE_LOCK = threading.Lock()

MESSAGE_TRACKER = {}
MESSAGE_TRACKER_LOCK = threading.Lock()
MESSAGE_SSE_CLIENTS = {}
MESSAGE_SSE_COUNTER = 0
MESSAGE_SSE_LOCK = threading.Lock()

CALL_REQUESTS = {}
CALL_SIGNALS = {}
call_lock = threading.Lock()

_webrtc_presence = {}
_presence_lock = threading.Lock()
_presence_callbacks = []

MSG_PENDING = "pending"
MSG_SENT = "sent"
MSG_DELIVERED = "delivered"
MSG_SEEN = "seen"

# ---------------------------------------------------------------------------
# WEBRTC PRESENCE HELPERS
# ---------------------------------------------------------------------------
def _get_webrtc_config():
    return {"presence_ttl": 60, "heartbeat_interval": 30, "cleanup_interval": 10, "max_missed_heartbeats": 2}

def _set_user_online(user_id, socket_id=None, webrtc=False):
    with _presence_lock:
        prev = _webrtc_presence.get(user_id, {}).get("online", False)
        _webrtc_presence[user_id] = {"last_seen": time.time(), "online": True, "socket_id": socket_id, "webrtc_connected": webrtc, "missed_heartbeats": 0}
        if not prev:
            for cb in _presence_callbacks:
                try: cb(user_id, True)
                except: pass

def _set_user_offline(user_id):
    with _presence_lock:
        if user_id in _webrtc_presence:
            _webrtc_presence[user_id]["online"] = False
            for cb in _presence_callbacks:
                try: cb(user_id, False)
                except: pass

def _process_heartbeat(user_id):
    with _presence_lock:
        if user_id not in _webrtc_presence:
            _set_user_online(user_id)
            return True
        _webrtc_presence[user_id]["last_seen"] = time.time()
        _webrtc_presence[user_id]["missed_heartbeats"] = 0
        return True

def _is_user_online(user_id):
    cfg = _get_webrtc_config()
    with _presence_lock:
        if user_id not in _webrtc_presence: return False
        status = _webrtc_presence[user_id]
        if not status.get("online"): return False
        return time.time() - status.get("last_seen", 0) < cfg["presence_ttl"]

def _get_user_status(user_id):
    cfg = _get_webrtc_config()
    with _presence_lock:
        status = _webrtc_presence.get(user_id, {})
        elapsed = time.time() - status.get("last_seen", 0) if status else 0
        return {"online": status.get("online", False) and elapsed < cfg["presence_ttl"], "last_seen": status.get("last_seen", 0), "webrtc_connected": status.get("webrtc_connected", False), "elapsed": elapsed}

def _get_batch_status(user_ids):
    return {uid: _is_user_online(uid) for uid in user_ids}

def _cleanup_presence():
    cfg = _get_webrtc_config()
    with _presence_lock:
        now = time.time()
        for uid, st in list(_webrtc_presence.items()):
            if now - st.get("last_seen", 0) > cfg["presence_ttl"] * cfg["max_missed_heartbeats"]:
                _webrtc_presence[uid]["online"] = False
                for cb in _presence_callbacks:
                    try: cb(uid, False)
                    except: pass

def _start_presence_cleanup():
    cfg = _get_webrtc_config()
    def run():
        while True:
            time.sleep(cfg["cleanup_interval"])
            _cleanup_presence()
    threading.Thread(target=run, daemon=True).start()

_start_presence_cleanup()

def get_db():
    app.logger.info(f"DB: host={DB_CONFIG['host']}, db={DB_CONFIG['database']}")
    conn = psycopg2.connect(
        host=DB_CONFIG["host"], user=DB_CONFIG["user"],
        password=DB_CONFIG["password"], database=DB_CONFIG["database"],
        port=DB_CONFIG["port"], sslmode=DB_CONFIG.get("sslmode", "disable"),
        connect_timeout=DB_CONFIG.get("connect_timeout", 10),
    )
    conn.autocommit = False
    return conn

def execute_query(query, params=None, fetch=False, commit=True, get_lastrowid=False):
    conn = None
    cur = None
    try:
        conn = get_db()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        cur.execute(query, params or ())
        if fetch:
            result = cur.fetchall()
            if commit:
                conn.commit()
            return result
        if get_lastrowid:
            conn.commit()
            return cur.fetchone().get("id") if cur.description else None
        if commit:
            conn.commit()
    except Psycopg2Error as e:
        app.logger.error(f"DB error: {e}")
        raise
    finally:
        if cur: cur.close()
        if conn: conn.close()

def get_user_by_email(email):
    rows = execute_query("SELECT * FROM users WHERE email = %s LIMIT 1", (email,), fetch=True)
    return rows[0] if rows else None

def get_user_by_id(uid):
    rows = execute_query("SELECT * FROM users WHERE id = %s LIMIT 1", (uid,), fetch=True)
    return rows[0] if rows else None

def get_auth_user_id():
    auth = request.headers.get('Authorization') or ''
    if not auth.startswith('Bearer '):
        return None
    token = auth.split(' ', 1)[1].strip()
    try:
        if isinstance(token, bytes):
            token = token.decode('utf-8')
        if (token.startswith("b'") and token.endswith("'")) or (token.startswith('b"') and token.endswith('"')):
            token = token[2:-1]
        if (token.startswith('"') and token.endswith('"')) or (token.startswith("'") and token.endswith("'")):
            token = token[1:-1]
        payload = jwt.decode(token, app.config['JWT_SECRET'], algorithms=[app.config.get('JWT_ALGO', 'HS256')])
        uid = payload.get('user_id') or payload.get('id') or payload.get('sub')
        return int(uid) if uid else None
    except Exception:
        return None

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def save_file(file, upload_dir):
    filename = secure_filename(file.filename)
    unique_filename = str(uuid.uuid4()) + "_" + filename
    file.save(os.path.join(upload_dir, unique_filename))
    if os.path.normpath(upload_dir) == os.path.normpath(UPLOADS_DIR):
        public_sub = "uploads"
    elif os.path.normpath(upload_dir) == os.path.normpath(PROFILE_DIR):
        public_sub = "profile"
    elif os.path.normpath(upload_dir) == os.path.normpath(STATUSES_DIR):
        public_sub = "statuses"
    elif os.path.normpath(upload_dir) == os.path.normpath(THREATS_DIR):
        public_sub = "threats"
    else:
        public_sub = os.path.basename(upload_dir)
    return f"/media/{public_sub}/{unique_filename}"

def column_exists(table_name, column_name):
    conn = None; cur = None
    try:
        conn = get_db(); cur = conn.cursor()
        cur.execute("SELECT 1 FROM information_schema.columns WHERE table_name=%s AND column_name=%s", (table_name, column_name))
        return cur.fetchone() is not None
    except Exception:
        return False
    finally:
        if cur: cur.close()
        if conn: conn.close()

def add_column_if_missing(table_name, column_name, column_def):
    try:
        if not column_exists(table_name, column_name):
            app.logger.info(f"Adding column {column_name} to {table_name}")
            execute_query(f"ALTER TABLE {table_name} ADD COLUMN {column_name} {column_def}", commit=True)
            return True
    except Exception as e:
        app.logger.exception(f"Failed to add column: {e}")
    return False

def check_rate_limit(user_id, max_per_second=10):
    key = str(user_id); now = time.time()
    if key not in _rate_limit_store:
        _rate_limit_store[key] = []
    _rate_limit_store[key] = [t for t in _rate_limit_store[key] if now - t < 1]
    if len(_rate_limit_store[key]) >= max_per_second:
        return False
    _rate_limit_store[key].append(now)
    return True

def _channel_id(a, b):
    return f"msg_{min(a,b)}_{max(a,b)}"

# ---------------------------------------------------------------------------
# FCM
# ---------------------------------------------------------------------------
def _load_service_account_credentials():
    sa = app.config.get('FCM_SERVICE_ACCOUNT')
    if not sa: return None
    try:
        if sa.strip().startswith('{'): return json.loads(sa)
        with open(sa, 'r', encoding='utf-8') as fh: return json.load(fh)
    except Exception:
        app.logger.exception('Failed to load service account info')
        return None

def _auto_config_service_account():
    if app.config.get('FCM_SERVICE_ACCOUNT'): return
    candidates = []
    try:
        candidates.extend(glob.glob(os.path.join(os.getcwd(), '*.json')))
        dl = Path.home() / 'Downloads'
        if dl.exists(): candidates.extend(glob.glob(str(dl / '*.json')))
        for p in candidates:
            try:
                with open(p, 'r', encoding='utf-8') as fh: j = json.load(fh)
                if isinstance(j, dict) and j.get('type') == 'service_account':
                    app.logger.info(f'Auto-configuring FCM from {p}')
                    app.config['FCM_SERVICE_ACCOUNT'] = str(p)
                    if not app.config.get('FCM_PROJECT_ID') and j.get('project_id'):
                        app.config['FCM_PROJECT_ID'] = j['project_id']
                    return
            except Exception: continue
    except Exception: pass
_auto_config_service_account()

def _get_fcm_v1_access_token():
    global _fcm_sa_credentials, _fcm_sa_token, _fcm_sa_token_expiry
    try:
        if not GOOGLE_AUTH_AVAILABLE: return None
        if _fcm_sa_credentials is None:
            info = _load_service_account_credentials()
            if not info: return None
            _fcm_sa_credentials = ga_service_account.Credentials.from_service_account_info(info, scopes=["https://www.googleapis.com/auth/firebase.messaging"])
        now = int(time.time())
        if _fcm_sa_token and _fcm_sa_token_expiry - 60 > now: return _fcm_sa_token
        req = ga_requests.Request(); _fcm_sa_credentials.refresh(req)
        _fcm_sa_token = _fcm_sa_credentials.token
        _fcm_sa_token_expiry = int(_fcm_sa_credentials.expiry.timestamp()) if _fcm_sa_credentials.expiry else now + 300
        return _fcm_sa_token
    except Exception:
        app.logger.exception('Failed to obtain FCM token')
        return None

def get_google_auth_request():
    try:
        if not GOOGLE_AUTH_AVAILABLE: return None
        info = _load_service_account_credentials()
        if not info: return None
        creds = ga_service_account.Credentials.from_service_account_info(info, scopes=["https://www.googleapis.com/auth/firebase.messaging"])
        req = ga_requests.Request(); creds.refresh(req)
        return creds.token
    except Exception:
        app.logger.exception('get_google_auth_request failed')
        return None

def send_fcm_request(token, title, body, data=None):
    try:
        sa = _load_service_account_credentials()
        if not sa or not GOOGLE_AUTH_AVAILABLE: return
        access_token = _get_fcm_v1_access_token()
        if not access_token: return
        project_id = app.config.get('FCM_PROJECT_ID') or sa.get('project_id')
        if not project_id: return
        url = FCM_V1_URL_TEMPLATE.format(project_id=project_id)
        if isinstance(data, dict):
            sn = data.get('sender_name') or data.get('sender_username') or data.get('sender') or data.get('senderName')
            if sn: title = str(sn)
        data_map = {k: str(v) for k, v in (data or {}).items()}
        if title is not None: data_map.setdefault('title', str(title))
        if body is not None: data_map.setdefault('body', str(body))
        body_obj = {'message': {'token': token, 'data': data_map, 'android': {'priority': 'HIGH'}}}
        req = urllib.request.Request(url, data=json.dumps(body_obj).encode('utf-8'), method='POST')
        req.add_header('Content-Type', 'application/json')
        req.add_header('Authorization', f'Bearer {access_token}')
        try:
            with urllib.request.urlopen(req, timeout=10) as resp:
                app.logger.debug(f'FCM response: {resp.read().decode("utf-8")}')
        except urllib.error.HTTPError as he:
            try: err = he.read().decode('utf-8')
            except: err = str(he)
            app.logger.error(f'FCM HTTPError: {he.code} {err}')
            try:
                j = json.loads(err) if err else {}
                details = j.get('error', {}).get('details', []) if isinstance(j, dict) else []
                for d in details:
                    if isinstance(d, dict) and d.get('@type','').endswith('FcmError') and d.get('errorCode') in ('UNREGISTERED',):
                        execute_query('DELETE FROM push_tokens WHERE token=%s', (token,), commit=True); break
            except: pass
    except Exception:
        app.logger.exception('FCM send error')

def send_fcm_message(user_id, title, body, data_payload=None):
    try:
        rows = execute_query("SELECT token FROM push_tokens WHERE user_id=%s", (user_id,), fetch=True)
        if not rows: return False
        token = rows[0].get('token')
        if not token: return False
        access_token = get_google_auth_request()
        if not access_token: return False
        project_id = app.config.get('FCM_PROJECT_ID') or 'vijaychat-70ca1'
        url = f'https://fcm.googleapis.com/v1/projects/{project_id}/messages:send'
        data_iter = {}
        if isinstance(data_payload, dict): data_iter = dict(data_payload)
        else:
            try: data_iter = json.loads(json.dumps(data_payload)) if data_payload is not None else {}
            except: data_iter = {}
        if not isinstance(data_iter, dict): data_iter = {}
        sender_name = data_iter.get('sender_name') or data_iter.get('sender_username') or data_iter.get('sender') or data_iter.get('senderName')
        if not sender_name:
            sid = data_iter.get('sender_id') or data_iter.get('senderId') or data_iter.get('sender_id_str')
            if sid:
                try:
                    u = get_user_by_id(int(sid))
                    if u: sender_name = u.get('username') or u.get('name')
                except: pass
        notif_title = sender_name or title
        notif_body = body
        data_block = {k: str(v) for k, v in data_iter.items()}
        data_block['title'] = str(notif_title)
        data_block['body'] = str(notif_body)
        if sender_name: data_block['sender_name'] = str(sender_name)
        payload = {'message': {'token': token, 'data': data_block, 'android': {'priority': 'HIGH'}}}
        headers = {'Authorization': f'Bearer {access_token}', 'Content-Type': 'application/json'}
        resp = requests.post(url, headers=headers, json=payload, timeout=10)
        if resp.status_code == 200: return True
        text = resp.text
        try:
            j = resp.json()
            for d in (j.get('error',{}).get('details',[]) or []):
                if isinstance(d,dict) and d.get('@type','').endswith('FcmError') and d.get('errorCode') in ('UNREGISTERED',):
                    execute_query('DELETE FROM push_tokens WHERE token=%s', (token,), commit=True); break
        except:
            if resp.status_code == 404 and 'UNREGISTERED' in text.upper():
                execute_query('DELETE FROM push_tokens WHERE token=%s', (token,), commit=True)
        return False
    except Exception:
        app.logger.exception('send_fcm_message failed'); return False

def send_fcm_to_user(user_id, payload):
    try:
        rows = execute_query("SELECT token FROM push_tokens WHERE user_id=%s", (user_id,), fetch=True)
        if not rows: return
        title = payload.get('sender_username') or 'New Message'
        body = (payload.get('content') or '')[:120] or 'New message'
        for r in rows:
            if r.get('token'): send_fcm_request(r['token'], title, body, payload)
    except Exception: app.logger.exception('send_fcm_to_user failed')

def _send_fcm_v1_notification(token, title, body, data=None):
    try:
        if not all([token, title, body]): return False
        if not GOOGLE_AUTH_AVAILABLE or not _load_service_account_credentials(): return False
        send_fcm_request(token, title, body, data or {})
        return True
    except: return False

# ---------------------------------------------------------------------------
# WEBSOCKET
# ---------------------------------------------------------------------------
async def ws_handler(websocket, path):
    user_id = None
    try:
        parsed = urlparse(path); qs = parse_qs(parsed.query)
        tokens = qs.get('token') or qs.get('jwt') or []
        if not tokens: await websocket.close(code=4001, reason='token required'); return
        token = tokens[0]
        try:
            payload = jwt.decode(token, app.config['JWT_SECRET'], algorithms=[app.config['JWT_ALGO']])
            user_id = str(payload.get('user_id'))
            if not user_id: await websocket.close(code=4002, reason='invalid token'); return
        except jwt.PyJWTError: await websocket.close(code=4003, reason='invalid token'); return
        with connected_lock: connected_clients.setdefault(user_id, set()).add(websocket)
        app.logger.info(f'WS connected user:{user_id}')
        async for raw in websocket:
            try:
                data = json.loads(raw); msg_type = data.get("t")
                if msg_type in ("delivered","delivered_batch"):
                    cids = data.get("cids",[data.get("cid")]); ldid=data.get("ldid"); conv=data.get("conv"); via=data.get("via","ws"); src=data.get("src","server")
                    if ldid and conv:
                        parts=conv.split("_")
                        if len(parts)==2:
                            sid,rid=int(parts[0]),int(parts[1])
                            receiver=sid if rid==int(user_id) else rid
                            execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<2",(receiver,int(user_id),ldid),commit=True)
                            publish_to_user(str(receiver),{"t":"delivered","conv":conv,"ldid":ldid,"v":2,"via":via,"src":src})
                    for cid in cids:
                        if not cid: continue
                        r=execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE client_id=%s AND version<2 RETURNING sender_id",(cid,),commit=True)
                        if r: publish_to_user(str(r[0]["sender_id"]),{"t":"delivered","cid":cid,"v":2,"via":via,"src":src})
                elif msg_type in ("seen","seen_range"):
                    conv=data.get("conv"); lsid=data.get("lsid"); from_id=data.get("from",lsid); via=data.get("via","ws"); src=data.get("src","server")
                    if conv and lsid:
                        parts=conv.split("_")
                        if len(parts)==2:
                            sid,rid=int(parts[0]),int(parts[1]); other=sid if rid==int(user_id) else rid; uid_int=int(user_id)
                            execute_query("UPDATE messages SET status='seen',version=3,status_updated_at=NOW() WHERE sender_id=%s AND receiver_id=%s AND id>=%s AND id<=%s AND version<3",(other,uid_int,from_id,lsid),commit=True)
                            publish_to_user(str(other),{"t":"seen","conv":conv,"lsid":lsid,"via":via,"src":src})
                elif msg_type=="status":
                    conv=data.get("conv"); ldid=data.get("ldid",0); lsid=data.get("lsid",0); via=data.get("via","ws"); src=data.get("src","server")
                    if conv:
                        parts=conv.split("_")
                        if len(parts)==2:
                            sid,rid=int(parts[0]),int(parts[1])
                            if ldid>0: execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<2",(rid,sid,ldid),commit=True)
                            if lsid>0 and lsid<=ldid: execute_query("UPDATE messages SET status='seen',version=3,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<3",(rid,sid,lsid),commit=True)
                            publish_to_user(str(sid),{"t":"status","conv":conv,"ldid":ldid,"lsid":lsid,"v":3,"via":via,"src":src})
            except (json.JSONDecodeError,Exception): pass
    except websockets.exceptions.ConnectionClosed: pass
    except Exception: app.logger.exception('WS handler error')
    finally:
        try:
            with connected_lock:
                conns=connected_clients.get(user_id)
                if conns and websocket in conns:
                    conns.remove(websocket)
                    if not conns: del connected_clients[user_id]
        except: pass

def start_ws_server(host='0.0.0.0', port=6789):
    global ws_loop
    def _run():
        loop=asyncio.new_event_loop(); asyncio.set_event_loop(loop)
        try: globals()['ws_loop']=loop
        except: pass
        server=loop.run_until_complete(websockets.serve(ws_handler,host,port))
        app.logger.info(f'WS server ws://{host}:{port}')
        try: loop.run_forever()
        finally: server.close(); loop.run_until_complete(server.wait_closed()); loop.close()
    threading.Thread(target=_run,daemon=True).start()

def publish_to_user(user_id, payload):
    try:
        with connected_lock: conns=list(connected_clients.get(str(user_id),[]))
        if not conns: return
        msg=json.dumps(payload)
        async def _send_all():
            to_remove=[]; sent=0
            for ws in conns:
                try: await ws.send(msg); sent+=1
                except: to_remove.append(ws)
            if to_remove:
                with connected_lock:
                    cur=connected_clients.get(str(user_id),set())
                    for r in to_remove:
                        if r in cur: cur.remove(r)
                    if not cur: connected_clients.pop(str(user_id),None)
        try:
            if ws_loop and getattr(ws_loop,'is_running',lambda:False)():
                future=asyncio.run_coroutine_threadsafe(_send_all(),ws_loop)
                future.add_done_callback(lambda f: app.logger.exception('WS pub error') if f.exception() else None)
            else:
                loop=asyncio.new_event_loop(); loop.run_until_complete(_send_all()); loop.close()
        except: app.logger.exception('Failed to schedule WS publish')
    except: app.logger.exception('Failed to publish WS message')

def sse_broadcast(user_id, event_type, data):
    with SSE_LOCK:
        for client in SSE_CLIENTS.get(user_id,[]):
            if "queue" in client: client["queue"].append(data)

def _broadcast_to_sse(user_id, event_type, data):
    with MESSAGE_SSE_LOCK:
        for client in MESSAGE_SSE_CLIENTS.get(str(user_id),[]):
            try: client["queue"].append({"event":event_type,"data":data})
            except: pass

# ---------------------------------------------------------------------------
# MIGRATIONS / STARTUP
# ---------------------------------------------------------------------------
def ensure_push_tokens_table():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS push_tokens (
            user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            token VARCHAR(500) NOT NULL, platform VARCHAR(50),
            last_updated TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            PRIMARY KEY (user_id, token));""", commit=True)
    except Exception: app.logger.exception('Failed to ensure push_tokens table')

def ensure_unread_table():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS unread_counts (
            receiver_id INTEGER NOT NULL, sender_id INTEGER NOT NULL,
            count INTEGER DEFAULT 0, PRIMARY KEY (receiver_id, sender_id));""", commit=True)
    except Exception: app.logger.exception('Failed to ensure unread_counts table')

def ensure_webrtc_messages_table():
    try:
        execute_query("""CREATE TABLE IF NOT EXISTS webrtc_messages (
            id SERIAL PRIMARY KEY,
            server_message_id VARCHAR(100) UNIQUE NOT NULL,
            client_message_id VARCHAR(100) UNIQUE NOT NULL,
            sender_id INTEGER NOT NULL,
            receiver_id INTEGER NOT NULL,
            content TEXT DEFAULT '',
            client_timestamp DOUBLE PRECISION,
            server_timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            files JSONB DEFAULT '[]',
            status VARCHAR(20) DEFAULT 'pending',
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP);""", commit=True)
    except Exception: app.logger.exception('Failed to ensure webrtc_messages table')

def migrate_statuses_base64_to_files():
    try:
        add_column_if_missing("statuses","file_path","VARCHAR(255) NULL")
        if not column_exists("statuses","file_base64") or not column_exists("statuses","file_path"): return
        rows=execute_query("SELECT id,file_base64,file_type FROM statuses WHERE file_base64 IS NOT NULL LIMIT 1000",fetch=True)
        if not rows: return
        for r in rows:
            sid=r["id"]; fb64=r.get("file_base64"); mime=r.get("file_type") or "application/octet-stream"
            if not fb64: continue
            try:
                data=base64.b64decode(fb64); ext="bin"
                if "/" in mime:
                    c=mime.split("/")[-1].split(";")[0]
                    if c: ext=c
                fname=f"{uuid.uuid4()}_status.{ext}"
                with open(os.path.join(STATUSES_DIR,fname),"wb") as fh: fh.write(data)
                execute_query("UPDATE statuses SET file_path=%s,file_base64=NULL WHERE id=%s",(f"/media/statuses/{fname}",sid),commit=True)
            except Exception as e: app.logger.exception(f"Failed migrating status id={sid}: {e}")
    except Exception as e: app.logger.exception("Migration failed")

# ---------------------------------------------------------------------------
# AUTH & USERS
# ---------------------------------------------------------------------------
@app.route("/login", methods=["POST"])
def login():
    try:
        data=request.json or {}; email=data.get("email"); password=data.get("password")
        if not email or not password: return jsonify({"error":"Email and password required"}),400
        user=get_user_by_email(email)
        if not user: return jsonify({"error":"User not found"}),404
        if not user.get("password"): return jsonify({"error":"No password set"}),400
        if not check_password_hash(user["password"],password): return jsonify({"error":"Password is incorrect"}),401
        user.pop("password",None)
        exp=datetime.datetime.now(datetime.timezone.utc)+datetime.timedelta(seconds=app.config.get('JWT_EXP_SECONDS',604800))
        token=jwt.encode({"user_id":user.get("id"),"exp":exp},app.config['JWT_SECRET'],algorithm=app.config['JWT_ALGO'])
        return jsonify({"message":"Login successful","user":user,"token":token}),200
    except Exception as e: return jsonify({"error":"Login failed","details":str(e)}),500

@app.route("/google-login", methods=["POST"])
def google_login():
    data=request.get_json(force=True) or {}; email=data.get("email"); name=data.get("name"); google_id=data.get("google_id")
    if not email or not name or not google_id: return jsonify({"error":"email, name, and google_id required"}),400
    try:
        existing=execute_query("SELECT id,username,name,email,google_id,sw_no FROM users WHERE email=%s LIMIT 1",(email,),fetch=True)
        if not existing:
            execute_query("INSERT INTO users (name,username,email,google_id,created_at) VALUES (%s,%s,%s,%s,%s)",(name,name,email,google_id,datetime.datetime.now(datetime.timezone.utc)),commit=True)
            new_user=execute_query("SELECT id,username,name,email,google_id,sw_no FROM users WHERE email=%s LIMIT 1",(email,),fetch=True)
            if not new_user: return jsonify({"error":"User creation failed"}),500
            user_row=new_user[0]
        else: user_row=existing[0]
        if user_row.get("sw_no"): return jsonify({"user":user_row,"registered":True}),200
        return jsonify({"email":email,"registered":False}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/register", methods=["POST"])
def register():
    data=request.get_json(force=True) or {}; email=data.get("email"); username=data.get("username"); sw_no=data.get("sw_no"); age=data.get("age"); gender=data.get("gender"); password=data.get("password")
    if not all([email,username,sw_no,age,gender,password]): return jsonify({"error":"All fields required"}),400
    try: age=int(age)
    except: return jsonify({"error":"Age must be integer"}),400
    try:
        if not execute_query("SELECT id FROM users WHERE email=%s LIMIT 1",(email,),fetch=True): return jsonify({"error":"Google login required first"}),400
        hashed=generate_password_hash(password)
        execute_query("UPDATE users SET username=%s,sw_no=%s,age=%s,gender=%s,password=%s,registration_date=%s WHERE email=%s",(username,sw_no,age,gender,hashed,datetime.datetime.now(datetime.timezone.utc),email),commit=True)
        profile=execute_query("SELECT id,username,sw_no,age,gender,email FROM users WHERE email=%s",(email,),fetch=True)
        return jsonify({"message":"Registered successfully","user":profile[0]}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/users", methods=["GET"])
def get_users():
    try:
        rows=execute_query("SELECT id,username,age,gender,email,sw_no,registration_date FROM users",fetch=True)
        return jsonify(rows),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/users/<int:uid>", methods=["GET"])
def get_user(uid):
    try:
        user=get_user_by_id(uid)
        if not user: return jsonify({"error":"User not found"}),404
        user.pop("password",None); return jsonify(user),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/users/<int:uid>", methods=["PUT"])
def update_user(uid):
    data=request.get_json(force=True) or {}; username=data.get("username"); sw_no=data.get("sw_no"); age=data.get("age"); gender=data.get("gender"); password=data.get("password")
    if not all([username,sw_no,age,gender]): return jsonify({"error":"username, sw_no, age, gender required"}),400
    try: age=int(age)
    except: return jsonify({"error":"Age must be integer"}),400
    try:
        if password:
            execute_query("UPDATE users SET username=%s,sw_no=%s,age=%s,gender=%s,password=%s WHERE id=%s",(username,sw_no,age,gender,generate_password_hash(password),uid),commit=True)
        else:
            execute_query("UPDATE users SET username=%s,sw_no=%s,age=%s,gender=%s WHERE id=%s",(username,sw_no,age,gender,uid),commit=True)
        return jsonify({"message":"User updated successfully"}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/profile/<int:user_id>", methods=["GET"])
def get_user_profile(user_id):
    try:
        user=execute_query("SELECT id,username,age,gender,email,sw_no,registration_date,profile_picture_url,bio,location,profile_picture_base64 FROM users WHERE id=%s LIMIT 1",(user_id,),fetch=True)
        if not user: return jsonify({"error":"User not found"}),404
        row=user[0]
        if isinstance(row.get("registration_date"),datetime.datetime): row["registration_date"]=row["registration_date"].isoformat()
        return jsonify(row),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/profile/<int:user_id>", methods=["PUT"])
def update_user_profile(user_id):
    try:
        data=request.form; bio=data.get("bio"); location=data.get("location"); pp_url=None
        if "profile_picture" in request.files:
            f=request.files["profile_picture"]
            if f and allowed_file(f.filename): pp_url=save_file(f,PROFILE_DIR)
            else: return jsonify({"error":"Invalid file format"}),400
        fields=[]; params=[]
        if bio is not None: fields.append("bio=%s"); params.append(bio)
        if location is not None: fields.append("location=%s"); params.append(location)
        if pp_url is not None: fields.append("profile_picture_url=%s"); params.append(pp_url)
        if not fields: return jsonify({"message":"No fields to update"}),200
        execute_query(f"UPDATE users SET {', '.join(fields)} WHERE id=%s",tuple(params+[user_id]),commit=True)
        return jsonify({"message":"User profile updated successfully"}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/delete_user/<int:user_id>", methods=["DELETE","OPTIONS"])
def delete_user(user_id):
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        for q in [
            "DELETE FROM friend_requests WHERE sender_id=%s OR receiver_id=%s",
            "DELETE FROM messages WHERE sender_id=%s OR receiver_id=%s",
            "DELETE FROM blocked_users WHERE blocker_id=%s OR blocked_id=%s",
            "DELETE FROM users WHERE id=%s",
        ]: execute_query(q,(user_id,user_id),commit=True)
        return jsonify({"message":"User deleted successfully"}),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# MESSAGES
# ---------------------------------------------------------------------------
@app.route("/messages/<int:sender_id>/<int:receiver_id>", methods=["GET"])
def get_messages(sender_id, receiver_id):
    try:
        after_id=request.args.get("after_id",type=int); limit=request.args.get("limit",default=50,type=int)
        if after_id:
            q="""SELECT m.id,m.client_id AS cid,m.sender_id AS sid,u1.username AS su,m.receiver_id AS rid,u2.username AS ru,m.content,m.reply_to_id AS rpid,m.files,m.status,m.version AS v,m.server_timestamp AS sts,m.status_updated_at AS uts,m.created_at AS ct FROM messages m JOIN users u1 ON m.sender_id=u1.id JOIN users u2 ON m.receiver_id=u2.id WHERE m.id>%s AND((m.sender_id=%s AND m.receiver_id=%s AND NOT m.deleted_by_sender)OR(m.sender_id=%s AND m.receiver_id=%s AND NOT m.deleted_by_receiver))ORDER BY m.id ASC LIMIT %s"""
            params=(after_id,sender_id,receiver_id,receiver_id,sender_id,limit)
        else:
            q="""SELECT m.id,m.client_id AS cid,m.sender_id AS sid,u1.username AS su,m.receiver_id AS rid,u2.username AS ru,m.content,m.reply_to_id AS rpid,m.files,m.status,m.version AS v,m.server_timestamp AS sts,m.status_updated_at AS uts,m.created_at AS ct FROM messages m JOIN users u1 ON m.sender_id=u1.id JOIN users u2 ON m.receiver_id=u2.id WHERE((m.sender_id=%s AND m.receiver_id=%s AND NOT m.deleted_by_sender)OR(m.sender_id=%s AND m.receiver_id=%s AND NOT m.deleted_by_receiver))ORDER BY m.created_at ASC LIMIT %s"""
            params=(sender_id,receiver_id,receiver_id,sender_id,limit)
        rows=execute_query(q,params,fetch=True)
        for r in rows:
            if isinstance(r.get("ct"),datetime.datetime): r["ct"]=r["ct"].isoformat()
            fv=r.get("files")
            if fv is None: r["files"]=[]
            elif isinstance(fv,str):
                try: r["files"]=json.loads(fv) if isinstance(json.loads(fv),list) else []
                except: r["files"]=[]
            else: r["files"]=fv
        return jsonify(rows),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/messages", methods=["POST"])
def send_message():
    try:
        sender_id=request.form.get("sender_id"); receiver_id=request.form.get("receiver_id"); content=request.form.get("content",""); reply_to_id=request.form.get("reply_to_id"); client_id=request.form.get("client_id")
        if sender_id and not check_rate_limit(int(sender_id),10): return jsonify({"error":"Rate limit exceeded"}),429
        if not sender_id or not receiver_id: return jsonify({"error":"sender_id and receiver_id required"}),400
        try: sender_id=int(sender_id); receiver_id=int(receiver_id)
        except: return jsonify({"error":"IDs must be integers"}),400
        reply_to_id=int(reply_to_id) if reply_to_id and str(reply_to_id).isdigit() else None
        files_data=[]
        if "files" in request.files:
            for f in request.files.getlist("files"):
                try:
                    if not f: continue
                    if not allowed_file(f.filename or ''): continue
                    fn=secure_filename(f.filename); ufn=str(uuid.uuid4())+"_"+fn; f.save(os.path.join(app.config['MESSAGES_FOLDER'],ufn))
                    files_data.append({"file_name":f.filename,"file_type":f.mimetype,"file_url":f"/media/uploads/{ufn}"})
                except Exception: app.logger.exception('file upload error')
        if execute_query("SELECT 1 FROM blocked_users WHERE (blocker_id=%s AND blocked_id=%s) OR (blocker_id=%s AND blocked_id=%s)",(sender_id,receiver_id,receiver_id,sender_id),fetch=True):
            return jsonify({"error":"Cannot send message, user is blocked"}),403
        result=execute_query("INSERT INTO messages (client_id,sender_id,receiver_id,content,reply_to_id,files,status,version,server_timestamp,status_updated_at) VALUES (%s,%s,%s,%s,%s,%s,'sent',1,NOW(),NOW()) RETURNING id,client_id",(client_id,sender_id,receiver_id,content,reply_to_id,json.dumps(files_data)),fetch=True,commit=True)
        message_id=result[0].get("id") if result else None; mc_id=result[0].get("client_id") if result else None
        fetched=None
        if message_id:
            fetched=execute_query("SELECT m.id,m.sender_id,u1.username AS sender_username,m.receiver_id,u2.username AS receiver_username,m.content,m.files,m.reply_to_id,m.created_at FROM messages m JOIN users u1 ON m.sender_id=u1.id JOIN users u2 ON m.receiver_id=u2.id WHERE m.id=%s LIMIT 1",(message_id,),fetch=True)
        payload=fetched[0] if fetched else {"id":message_id,"sender_id":sender_id,"receiver_id":receiver_id,"content":content,"files":files_data}
        if isinstance(payload,dict):
            if not payload.get('sender_name') and payload.get('sender_username'): payload['sender_name']=payload['sender_username']
            if not payload.get('sender_username') and payload.get('sender_name'): payload['sender_username']=payload['sender_name']
        delivery="none"
        try:
            publish_to_user(str(receiver_id),payload); delivery="websocket"
            if message_id: execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE id=%s AND version<2",(message_id,),commit=True)
            publish_to_user(str(sender_id),{"t":"delivered","conv":f"{min(sender_id,receiver_id)}_{max(sender_id,receiver_id)}","id":message_id,"cid":mc_id or str(message_id),"v":2})
        except: app.logger.exception('WS delivery failed')
        if delivery=="none":
            try: send_fcm_message(receiver_id,payload.get('sender_username') or 'New Message',(payload.get('content') or '')[:120] or 'New message',payload)
            except: pass
        try: execute_query("INSERT INTO unread_counts (receiver_id,sender_id,count) VALUES (%s,%s,1) ON CONFLICT (receiver_id,sender_id) DO UPDATE SET count=unread_counts.count+1",(receiver_id,sender_id),commit=True)
        except: pass
        resp=jsonify({"message":"Message sent","id":message_id,"files":files_data}); resp.headers['X-Via-WebRTC']='false'; return resp,201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/messages/mark_read", methods=["POST"])
def mark_messages_read():
    try:
        data=request.get_json(force=True) or {}; user_id=data.get("user_id"); other_id=data.get("other_id"); last_seen_id=data.get("last_seen_id")
        if not user_id or not other_id: return jsonify({"error":"user_id and other_id required"}),400
        if not last_seen_id: return jsonify({"error":"last_seen_id required"}),400
        conn=get_db(); cur=conn.cursor(cursor_factory=RealDictCursor)
        try:
            cur.execute("UPDATE messages SET status='seen',version=3,status_updated_at=NOW() WHERE sender_id=%s AND receiver_id=%s AND id<=%s AND version<3",(other_id,user_id,last_seen_id))
            affected=cur.rowcount; conn.commit()
            if affected>0: publish_to_user(str(other_id),{"t":"seen","conv":f"{other_id}_{user_id}","lsid":last_seen_id})
        finally: cur.close(); conn.close()
        try: execute_query("DELETE FROM unread_counts WHERE receiver_id=%s AND sender_id=%s",(user_id,other_id),commit=True); publish_to_user(str(user_id),{"type":"unread_cleared","sender_id":str(other_id),"marked_count":int(affected)})
        except: pass
        return jsonify({"message":"marked read","marked_count":int(affected)}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/messages", methods=["DELETE"])
def delete_messages():
    try:
        data=request.json or {}; ids=data.get("message_ids"); uid=data.get("user_id"); both=data.get("both_sides",False)
        if not ids or not uid: return jsonify({"error":"Message IDs and user ID required"}),400
        try: uid=int(uid); ids=[int(x) for x in ids]
        except: return jsonify({"error":"IDs must be integers"}),400
        ph=",".join(["%s"]*len(ids))
        if both: execute_query(f"DELETE FROM messages WHERE id IN ({ph})",tuple(ids),commit=True)
        else:
            execute_query(f"UPDATE messages SET deleted_by_receiver=true WHERE id IN ({ph}) AND receiver_id=%s",tuple(ids)+(uid,),commit=True)
            execute_query(f"UPDATE messages SET deleted_by_sender=true WHERE id IN ({ph}) AND sender_id=%s",tuple(ids)+(uid,),commit=True)
        return jsonify({"message":"Messages deleted successfully"}),200
    except Exception as e: return jsonify({"error":"An error occurred","details":str(e)}),500

@app.route('/debug/all_messages', methods=['GET'])
def debug_all_messages():
    try:
        rows=execute_query("SELECT id,sender_id,receiver_id,content,created_at FROM messages ORDER BY id DESC LIMIT 100",fetch=True)
        return jsonify({"count":len(rows),"messages":rows}),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# UNREAD COUNTS
# ---------------------------------------------------------------------------
@app.route('/unread_counts/<int:user_id>', methods=['GET'])
def get_unread_counts(user_id):
    try:
        if get_auth_user_id()!=user_id: return jsonify({"error":"unauthorized"}),401
        rows=execute_query("SELECT sender_id,count FROM unread_counts WHERE receiver_id=%s",(user_id,),fetch=True)
        return jsonify({"unread":{str(r['sender_id']):int(r['count']) for r in rows}} if rows else {"unread":{}}),200
    except: return jsonify({"error":"internal"}),500

@app.route('/unread/increment', methods=['POST'])
def increment_unread():
    try:
        data=request.get_json(force=True) or {}; rid=data.get('receiver_id'); sid=data.get('sender_id')
        if not rid or not sid: return jsonify({"error":"missing fields"}),400
        au=get_auth_user_id()
        if not au: return jsonify({"error":"unauthorized"}),401
        if au!=int(sid): return jsonify({"error":"forbidden"}),403
        execute_query("INSERT INTO unread_counts (receiver_id,sender_id,count) VALUES (%s,%s,1) ON CONFLICT (receiver_id,sender_id) DO UPDATE SET count=unread_counts.count+1",(rid,sid),commit=True)
        rows=execute_query("SELECT count FROM unread_counts WHERE receiver_id=%s AND sender_id=%s",(rid,sid),fetch=True)
        publish_to_user(str(rid),{"type":"unread_update","sender_id":str(sid),"count":int(rows[0]['count']) if rows else 0})
        return jsonify({"ok":True}),200
    except: return jsonify({"error":"internal"}),500

@app.route('/unread/clear', methods=['POST'])
def clear_unread():
    try:
        data=request.get_json(force=True) or {}; uid=data.get('user_id'); cid=data.get('contact_id')
        if not uid or not cid: return jsonify({"error":"missing fields"}),400
        if get_auth_user_id()!=int(uid): return jsonify({"error":"unauthorized"}),401
        execute_query("DELETE FROM unread_counts WHERE receiver_id=%s AND sender_id=%s",(uid,cid),commit=True)
        return jsonify({"ok":True}),200
    except: return jsonify({"error":"internal"}),500

# ---------------------------------------------------------------------------
# FRIEND REQUESTS
# ---------------------------------------------------------------------------
@app.route("/friend-request", methods=["POST"])
def send_friend_request():
    try:
        data=request.get_json(silent=True) or {}; sid=data.get("sender_id"); sw=data.get("sw_no")
        if not sid or not sw: return jsonify({"error":"sender_id and sw_no required"}),400
        recv=execute_query("SELECT id,username FROM users WHERE sw_no=%s LIMIT 1",(sw,),fetch=True)
        if not recv: return jsonify({"error":"User not found with this SW number"}),404
        rid=recv[0]["id"]
        if rid==sid: return jsonify({"error":"Cannot send to yourself"}),400
        if execute_query("SELECT 1 FROM blocked_users WHERE (blocker_id=%s AND blocked_id=%s) OR (blocker_id=%s AND blocked_id=%s) LIMIT 1",(sid,rid,rid,sid),fetch=True):
            return jsonify({"error":"User is blocked"}),403
        if execute_query("SELECT 1 FROM friend_requests WHERE ((sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s)) AND status='accepted' LIMIT 1",(sid,rid,rid,sid),fetch=True):
            return jsonify({"error":"Already friends"}),400
        ex=execute_query("SELECT id,status FROM friend_requests WHERE (sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s) ORDER BY id DESC LIMIT 1",(sid,rid,rid,sid),fetch=True)
        if ex and ex[0]["status"]=="pending": return jsonify({"error":"Pending request exists"}),400
        res=execute_query("INSERT INTO friend_requests (sender_id,receiver_id,status,created_at) VALUES (%s,%s,'pending',%s) RETURNING id",(sid,rid,datetime.datetime.now(datetime.timezone.utc)),commit=True,fetch=True)
        if not res: return jsonify({"error":"Insert failed"}),500
        created=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(res[0]["id"],),fetch=True)
        return jsonify(created[0]),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/friend-requests/<int:user_id>", methods=["GET"])
def get_friend_requests(user_id):
    try:
        inc=execute_query("SELECT f.id,f.status,s.id as sender_id,s.username as sender_name,s.sw_no as sender_sw FROM friend_requests f JOIN users s ON s.id=f.sender_id WHERE f.receiver_id=%s AND f.status='pending' ORDER BY f.id DESC",(user_id,),fetch=True)
        out=execute_query("SELECT f.id,f.status,r.id as receiver_id,r.username as receiver_name,r.sw_no as receiver_sw FROM friend_requests f JOIN users r ON r.id=f.receiver_id WHERE f.sender_id=%s AND f.status='pending' ORDER BY f.id DESC",(user_id,),fetch=True)
        return jsonify({"incoming":inc,"outgoing":out}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/friend-requests/<int:req_id>/accept", methods=["POST"])
def accept_friend_request(req_id):
    try:
        execute_query("UPDATE friend_requests SET status='accepted' WHERE id=%s AND status='pending'",(req_id,),commit=True)
        u=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(req_id,),fetch=True)
        if not u: return jsonify({"error":"Request not found"}),404
        return jsonify(u[0]),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/friend-requests/<int:req_id>/reject", methods=["POST"])
def reject_friend_request(req_id):
    try:
        execute_query("UPDATE friend_requests SET status='rejected' WHERE id=%s AND status='pending'",(req_id,),commit=True)
        u=execute_query("SELECT * FROM friend_requests WHERE id=%s LIMIT 1",(req_id,),fetch=True)
        if not u: return jsonify({"error":"Request not found"}),404
        return jsonify(u[0]),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/friends/<int:user_id>", methods=["GET"])
def get_friends(user_id):
    try:
        f=execute_query("SELECT u.id,u.username,u.age,u.gender,u.email,u.sw_no,u.registration_date FROM users u JOIN friend_requests f ON((f.sender_id=u.id AND f.receiver_id=%s) OR (f.receiver_id=u.id AND f.sender_id=%s)) WHERE f.status='accepted'",(user_id,user_id),fetch=True)
        return jsonify(f),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/remove_friend", methods=["POST","OPTIONS"])
def remove_friend():
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        data=request.json or {}; uid=data.get("user_id"); fid=data.get("friend_id")
        if not uid or not fid: return jsonify({"error":"user_id and friend_id required"}),400
        execute_query("DELETE FROM friend_requests WHERE (sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s)",(uid,fid,fid,uid),commit=True)
        return jsonify({"message":"Friend removed successfully"}),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# BLOCK / UNBLOCK
# ---------------------------------------------------------------------------
@app.route("/block_user", methods=["POST","OPTIONS"])
def block_user():
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        data=request.json or {}; b1=data.get("blocker_id"); b2=data.get("blocked_id")
        if not b1 or not b2: return jsonify({"error":"blocker_id and blocked_id required"}),400
        try: execute_query("INSERT INTO blocked_users (blocker_id,blocked_id) VALUES (%s,%s)",(b1,b2),commit=True)
        except Psycopg2IntegrityError: pass
        return jsonify({"message":"User blocked successfully"}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/is_blocked", methods=["GET"])
def is_blocked():
    b1=request.args.get("blocker_id"); b2=request.args.get("blocked_id")
    if not b1 or not b2: return jsonify({"error":"blocker_id and blocked_id required"}),400
    try:
        r=execute_query("SELECT EXISTS(SELECT 1 FROM blocked_users WHERE blocker_id=%s AND blocked_id=%s) AS is_blocked",(b1,b2),fetch=True)
        return jsonify({"is_blocked":bool(r and r[0].get("is_blocked"))}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/unblock_user", methods=["POST","OPTIONS"])
def unblock_user():
    if request.method=="OPTIONS": return jsonify({"message":"OK"}),200
    try:
        data=request.json or {}; b1=data.get("blocker_id"); b2=data.get("blocked_id")
        if not b1 or not b2: return jsonify({"error":"blocker_id and blocked_id required"}),400
        execute_query("DELETE FROM blocked_users WHERE blocker_id=%s AND blocked_id=%s",(b1,b2),commit=True)
        return jsonify({"message":"User unblocked successfully"}),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# FCM / PUSH TOKENS
# ---------------------------------------------------------------------------
@app.route('/register_fcm', methods=['POST'])
def register_fcm():
    try:
        data=request.get_json(silent=True)
        if not data: return jsonify({'error':'Invalid JSON'}),400
        uid=data.get('user_id'); tok=data.get('token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        try: execute_query('INSERT INTO push_tokens (user_id,token,platform,created_at) VALUES (%s,%s,%s,NOW())',(uid,tok,plat),commit=True)
        except:
            try: execute_query('UPDATE push_tokens SET user_id=%s,platform=%s WHERE token=%s',(uid,plat,tok),commit=True)
            except: pass
        return jsonify({'message':'registered'}),201
    except: return jsonify({'error':'internal error'}),500

@app.route('/register_token', methods=['POST'])
def register_token():
    try:
        data=request.get_json(silent=True) or request.form or {}
        uid=data.get('user_id') or data.get('userId') or data.get('uid'); tok=data.get('token') or data.get('fcm_token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        try: execute_query('INSERT INTO push_tokens (user_id,token,platform,created_at) VALUES (%s,%s,%s,NOW())',(int(uid),tok,plat),commit=True)
        except:
            try: execute_query('UPDATE push_tokens SET user_id=%s,platform=%s,created_at=NOW() WHERE token=%s',(int(uid),plat,tok),commit=True)
            except: return jsonify({'error':'db error'}),500
        return jsonify({'message':'registered'}),201
    except: return jsonify({'error':'internal error'}),500

@app.route("/register_push_token", methods=["POST"])
def register_push_token():
    data=request.get_json() or {}; uid=data.get("user_id"); tok=data.get("token")
    if not uid or not tok: return jsonify({"success":False,"error":"Missing fields"}),400
    try:
        execute_query("INSERT INTO push_tokens (user_id,token) VALUES (%s,%s) ON CONFLICT (user_id,token) DO UPDATE SET token=EXCLUDED.token",(uid,tok),commit=True)
        return jsonify({"success":True}),200
    except: return jsonify({"success":False,"error":"DB error"}),500

@app.route('/update_fcm_token', methods=['POST'])
def update_fcm_token():
    try:
        data=request.get_json(silent=True) or request.form or {}
        uid=data.get('user_id') or data.get('uid'); tok=data.get('token') or data.get('fcm_token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        try: execute_query("INSERT INTO push_tokens (user_id,token,platform) VALUES (%s,%s,%s) ON CONFLICT (user_id,token) DO UPDATE SET platform=EXCLUDED.platform",(int(uid),tok,plat),commit=True)
        except: return jsonify({'error':'db error'}),500
        return jsonify({'message':'token updated'}),200
    except: return jsonify({'error':'internal error'}),500

@app.route('/api/v1/fcm_token', methods=['POST'])
def api_fcm_token():
    try:
        data=request.get_json(silent=True) or {}
        uid=data.get('user_id') or data.get('userId'); tok=data.get('token') or data.get('fcm_token'); plat=data.get('platform')
        if not uid or not tok: return jsonify({'error':'user_id and token required'}),400
        execute_query("INSERT INTO push_tokens (user_id,token,platform) VALUES (%s,%s,%s) ON CONFLICT (user_id,token) DO UPDATE SET platform=EXCLUDED.platform",(int(uid),tok,plat),commit=True)
        return jsonify({'message':'ok'}),200
    except: return jsonify({'error':'internal error'}),500

@app.route('/test_fcm', methods=['POST'])
def test_fcm():
    try:
        data=request.get_json(silent=True)
        if not data: return jsonify({'error':'Invalid JSON'}),400
        tok=data.get("token"); title=data.get("title"); body=data.get("body")
        if not all([tok,title,body]): return jsonify({'error':'token, title, body required'}),400
        if not GOOGLE_AUTH_AVAILABLE or not app.config.get('FCM_SERVICE_ACCOUNT'): return jsonify({'error':'FCM not configured'}),503
        ok=_send_fcm_v1_notification(tok,title,body,data.get("data",{}))
        return (jsonify({"message":"FCM test sent"}),200) if ok else (jsonify({'error':'send failed'}),500)
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# STATUSES (STORIES)
# ---------------------------------------------------------------------------
@app.route('/statuses/upload', methods=['POST'])
def upload_status():
    try:
        uid=request.form.get("user_id"); file=request.files.get("status_file")
        if not uid or not file: return jsonify({"error":"Missing required fields"}),400
        if not allowed_file(file.filename): return jsonify({"error":"File extension not allowed"}),400
        add_column_if_missing("statuses","file_path","VARCHAR(255) NULL"); use_fp=column_exists("statuses","file_path"); use_b64=column_exists("statuses","file_base64")
        fp=None
        try: fp=save_file(file,STATUSES_DIR)
        except: app.logger.exception("save failed")
        if fp and use_fp:
            q="INSERT INTO statuses (user_id,file_path,file_type,created_at) VALUES (%s,%s,%s,%s)"
            p=(int(uid),fp,("video" if file.mimetype.startswith("video/") else "image"),datetime.datetime.now(datetime.timezone.utc))
        elif use_b64:
            b64=base64.b64encode(file.read()).decode("utf-8")
            q="INSERT INTO statuses (user_id,file_base64,file_type,created_at) VALUES (%s,%s,%s,%s)"
            p=(int(uid),b64,("video" if file.mimetype.startswith("video/") else "image"),datetime.datetime.now(datetime.timezone.utc))
        else:
            q="INSERT INTO statuses (user_id,file_type,created_at) VALUES (%s,%s,%s)"
            p=(int(uid),("video" if file.mimetype.startswith("video/") else "image"),datetime.datetime.now(datetime.timezone.utc))
        lid=execute_query(q,p,get_lastrowid=True)
        return jsonify({"message":"Status created","id":lid}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route('/statuses/<int:user_id>', methods=['GET'])
def get_statuses(user_id):
    try:
        fp_expr="s.file_path AS file_path" if column_exists("statuses","file_path") else "NULL AS file_path"
        b64_expr="s.file_base64 AS file_base64" if column_exists("statuses","file_base64") else "NULL AS file_base64"
        q=f"""SELECT s.id,s.user_id,{fp_expr},{b64_expr},s.file_type,s.created_at,u.username FROM statuses s JOIN users u ON u.id=s.user_id WHERE (s.user_id=%s OR s.user_id IN (SELECT CASE WHEN f.sender_id=%s THEN f.receiver_id WHEN f.receiver_id=%s THEN f.sender_id END FROM friend_requests f WHERE (f.sender_id=%s OR f.receiver_id=%s) AND f.status='accepted')) AND s.created_at>=NOW()-INTERVAL '24 hours' ORDER BY s.created_at DESC"""
        rows=execute_query(q,(user_id,user_id,user_id,user_id,user_id),fetch=True)
        for r in rows:
            if isinstance(r.get("created_at"),datetime.datetime): r["created_at"]=r["created_at"].isoformat()
        return jsonify(rows),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# THREATS (SOCIAL FEED)
# ---------------------------------------------------------------------------
@app.route("/threats", methods=["GET"])
def get_threats():
    try:
        mp="t.media_path AS media_path" if column_exists("threats","media_path") else ("t.media_url AS media_path" if column_exists("threats","media_url") else "NULL AS media_path")
        mm="t.media_mimetype AS media_mimetype" if column_exists("threats","media_mimetype") else ("t.media_mime AS media_mimetype" if column_exists("threats","media_mime") else "NULL AS media_mimetype")
        mp_col="t.media_path" if column_exists("threats","media_path") else ("t.media_url" if column_exists("threats","media_url") else "NULL")
        mm_col="t.media_mimetype" if column_exists("threats","media_mimetype") else ("t.media_mime" if column_exists("threats","media_mime") else "NULL")
        q=f"""SELECT t.id,t.user_id,t.content,t.media_url,{mp},{mm},t.created_at,u.username,u.profile_picture_url,COALESCE(COUNT(tl.user_id),0) AS like_count FROM threats t JOIN users u ON t.user_id=u.id LEFT JOIN threat_likes tl ON t.id=tl.threat_id GROUP BY t.id,t.user_id,t.content,t.media_url,{mp_col},{mm_col},t.created_at,u.username,u.profile_picture_url ORDER BY t.created_at DESC"""
        rows=execute_query(q,fetch=True)
        for r in rows:
            if isinstance(r.get("created_at"),datetime.datetime): r["created_at"]=r["created_at"].isoformat()
        return jsonify(rows),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/threats", methods=["POST"])
def create_threat():
    try:
        uid=request.form.get("user_id"); content=request.form.get("content","").strip()
        if not uid: return jsonify({"error":"User ID required"}),400
        if not content and "media" not in request.files: return jsonify({"error":"Content or media required"}),400
        mp=None; mm=None
        if "media" in request.files:
            f=request.files["media"]
            if f and allowed_file(f.filename): mp=save_file(f,THREATS_DIR); mm=f.mimetype
            else: return jsonify({"error":"Invalid file format"}),400
        if column_exists("threats","media_path"):
            q="INSERT INTO threats (user_id,content,media_path,media_mimetype,created_at) VALUES (%s,%s,%s,%s,%s)"; p=(uid,content or None,mp,mm,datetime.datetime.now(datetime.timezone.utc))
        elif column_exists("threats","media_url"):
            q="INSERT INTO threats (user_id,content,media_url,media_mimetype,created_at) VALUES (%s,%s,%s,%s,%s)"; p=(uid,content or None,mp,mm,datetime.datetime.now(datetime.timezone.utc))
        else:
            q="INSERT INTO threats (user_id,content,media_mimetype,created_at) VALUES (%s,%s,%s,%s)"; p=(uid,content or None,mm,datetime.datetime.now(datetime.timezone.utc))
        lid=execute_query(q,p,get_lastrowid=True)
        return jsonify({"message":"Threat created","id":lid}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/threats/<int:threat_id>/like", methods=["POST"])
def like_threat(threat_id):
    try:
        uid=request.json.get("user_id")
        if not uid: return jsonify({"error":"User ID required"}),400
        if execute_query("SELECT 1 FROM threat_likes WHERE user_id=%s AND threat_id=%s LIMIT 1",(uid,threat_id),fetch=True):
            execute_query("DELETE FROM threat_likes WHERE user_id=%s AND threat_id=%s",(uid,threat_id),commit=True)
            return jsonify({"message":"Threat unliked"}),200
        execute_query("INSERT INTO threat_likes (user_id,threat_id) VALUES (%s,%s)",(uid,threat_id),commit=True)
        return jsonify({"message":"Threat liked"}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/threats/<int:threat_id>/comments", methods=["GET"])
def get_comments(threat_id):
    try:
        uid=request.args.get("user_id")
        rows=execute_query("""SELECT c.id,c.user_id,c.comment,c.created_at,u.username,c.parent_comment_id,(SELECT COUNT(*) FROM comment_likes WHERE comment_id=c.id) AS like_count,EXISTS(SELECT 1 FROM comment_likes WHERE comment_id=c.id AND user_id=%s) AS liked_by_user,c.black_heart_count,EXISTS(SELECT 1 FROM comment_black_hearts WHERE user_id=%s AND comment_id=c.id) AS has_black_hearted FROM comments c JOIN users u ON c.user_id=u.id WHERE c.threat_id=%s ORDER BY c.created_at DESC""",(uid,uid,threat_id),fetch=True)
        for r in rows:
            if isinstance(r.get("created_at"),datetime.datetime): r["created_at"]=r["created_at"].isoformat()
        return jsonify(rows),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/threats/<int:threat_id>/comments", methods=["POST"])
def add_comment(threat_id):
    try:
        uid=request.json.get("user_id"); comment=request.json.get("comment")
        if not uid or not comment: return jsonify({"error":"User ID and comment required"}),400
        lid=execute_query("INSERT INTO comments (threat_id,user_id,comment,created_at) VALUES (%s,%s,%s,%s)",(threat_id,uid,comment,datetime.datetime.now(datetime.timezone.utc)),get_lastrowid=True)
        nc=execute_query("SELECT id,user_id,comment,created_at FROM comments WHERE id=%s",(lid,),fetch=True)
        if nc:
            u=execute_query("SELECT username FROM users WHERE id=%s",(uid,),fetch=True)
            nc[0]["username"]=u[0]["username"] if u else None
            if isinstance(nc[0].get("created_at"),datetime.datetime): nc[0]["created_at"]=nc[0]["created_at"].isoformat()
        return jsonify(nc[0]),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/comments/<int:comment_id>/like", methods=["POST"])
def like_comment(comment_id):
    try:
        uid=request.json.get("user_id")
        if not uid: return jsonify({"error":"User ID required"}),400
        if execute_query("SELECT 1 FROM comment_likes WHERE user_id=%s AND comment_id=%s LIMIT 1",(uid,comment_id),fetch=True):
            execute_query("DELETE FROM comment_likes WHERE user_id=%s AND comment_id=%s",(uid,comment_id),commit=True)
            return jsonify({"message":"Comment unliked"}),200
        execute_query("INSERT INTO comment_likes (user_id,comment_id) VALUES (%s,%s)",(uid,comment_id),commit=True)
        return jsonify({"message":"Comment liked"}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/comments/<int:comment_id>/replies", methods=["POST"])
def add_reply(comment_id):
    try:
        uid=request.json.get("user_id"); comment=request.json.get("comment")
        if not uid: return jsonify({"error":"User ID required"}),400
        parent=execute_query("SELECT threat_id FROM comments WHERE id=%s LIMIT 1",(comment_id,),fetch=True)
        if not parent: return jsonify({"error":"Parent not found"}),404
        tid=parent[0]["threat_id"]
        lid=execute_query("INSERT INTO comments (threat_id,user_id,comment,created_at,parent_comment_id) VALUES (%s,%s,%s,%s,%s)",(tid,uid,comment,datetime.datetime.now(datetime.timezone.utc),comment_id),get_lastrowid=True)
        nc=execute_query("SELECT id,user_id,comment,created_at,parent_comment_id FROM comments WHERE id=%s",(lid,),fetch=True)
        if nc:
            u=execute_query("SELECT username FROM users WHERE id=%s",(uid,),fetch=True)
            nc[0]["username"]=u[0]["username"] if u else None
            if isinstance(nc[0].get("created_at"),datetime.datetime): nc[0]["created_at"]=nc[0]["created_at"].isoformat()
        return jsonify(nc[0]),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/comments/<int:comment_id>/red_heart", methods=["POST"])
def red_heart_comment(comment_id):
    try:
        uid=request.json.get("user_id")
        if not uid: return jsonify({"error":"User ID required"}),400
        if execute_query("SELECT 1 FROM comment_red_hearts WHERE user_id=%s AND comment_id=%s LIMIT 1",(uid,comment_id),fetch=True):
            return jsonify({"message":"Already given red heart"}),400
        try:
            execute_query("INSERT INTO comment_red_hearts (user_id,comment_id,created_at) VALUES (%s,%s,%s)",(uid,comment_id,datetime.datetime.now(datetime.timezone.utc)),commit=True)
            return jsonify({"message":"Red heart added"}),201
        except Psycopg2IntegrityError: return jsonify({"error":"Already given"}),400
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/comments/<int:comment_id>/black_heart", methods=["POST"])
def black_heart_comment(comment_id):
    try:
        uid=request.json.get("user_id")
        if not uid: return jsonify({"error":"User ID required"}),400
        conn=get_db(); cur=conn.cursor(cursor_factory=RealDictCursor)
        try:
            cur.execute("SELECT 1 FROM comment_black_hearts WHERE user_id=%s AND comment_id=%s LIMIT 1",(uid,comment_id))
            ex=cur.fetchone()
            if ex:
                cur.execute("DELETE FROM comment_black_hearts WHERE user_id=%s AND comment_id=%s",(uid,comment_id))
                cur.execute("UPDATE comments SET black_heart_count=black_heart_count-1 WHERE id=%s",(comment_id,))
                cur.execute("DELETE FROM comment_red_hearts WHERE id IN (SELECT id FROM comment_red_hearts WHERE comment_id=%s ORDER BY created_at ASC LIMIT 2)",(comment_id,))
                msg="Black heart removed"
            else:
                cur.execute("INSERT INTO comment_black_hearts (user_id,comment_id,created_at) VALUES (%s,%s,%s)",(uid,comment_id,datetime.datetime.now(datetime.timezone.utc)))
                cur.execute("UPDATE comments SET black_heart_count=black_heart_count+1 WHERE id=%s",(comment_id,))
                msg="Black heart added"
            cur.execute("SELECT black_heart_count FROM comments WHERE id=%s",(comment_id,))
            res=cur.fetchone()
            if not res: conn.rollback(); return jsonify({"error":"Comment not found"}),404
            if res.get("black_heart_count",0)>=100:
                cur.execute("DELETE FROM comments WHERE id=%s",(comment_id,)); conn.commit()
                return jsonify({"message":"Comment deleted (black heart limit)"}),200
            conn.commit(); return jsonify({"message":msg}),200
        except Exception as e: conn.rollback(); return jsonify({"error":str(e)}),500
        finally: cur.close(); conn.close()
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/comments/<int:comment_id>", methods=["GET"])
def get_comment(comment_id):
    try:
        rows=execute_query("SELECT c.id,c.user_id,c.comment,c.created_at,u.username,c.parent_comment_id,(SELECT COUNT(*) FROM comment_likes WHERE comment_id=c.id) AS like_count,c.black_heart_count FROM comments c JOIN users u ON c.user_id=u.id WHERE c.id=%s",(comment_id,),fetch=True)
        if not rows: return jsonify({"error":"Comment not found"}),404
        r=rows[0]
        if isinstance(r.get("created_at"),datetime.datetime): r["created_at"]=r["created_at"].isoformat()
        return jsonify(r),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# MEDIA SERVING
# ---------------------------------------------------------------------------
@app.route("/media/uploads/<path:filename>", methods=["GET"])
def media_uploads(filename): return send_from_directory(UPLOADS_DIR,filename,conditional=True)

@app.route("/media/profile/<path:filename>", methods=["GET"])
def media_profile(filename): return send_from_directory(PROFILE_DIR,filename,conditional=True)

@app.route("/media/statuses/<path:filename>", methods=["GET"])
def media_statuses(filename): return send_from_directory(STATUSES_DIR,filename,conditional=True)

@app.route("/media/threats/<path:filename>", methods=["GET"])
def media_threats(filename): return send_from_directory(THREATS_DIR,filename,conditional=True)

# ---------------------------------------------------------------------------
# CALL / WEBRTC SIGNALING (IN-MEMORY)
# ---------------------------------------------------------------------------
@app.route("/home", methods=["GET"])
def home(): return jsonify({"status":"server running"})

@app.route("/test", methods=["GET"])
def test(): return "OK"

@app.route("/health", methods=["GET"])
def health_check():
    try: conn=get_db(); conn.close(); db="healthy"
    except: db="unhealthy"
    return jsonify({"status":"healthy","database":db,"ws_connections":len(connected_clients),"active":True})

@app.route("/call/request", methods=["POST"])
def call_request():
    try:
        data=request.json or {}; caller=data.get("caller_id"); callee=data.get("callee_id")
        if not caller or not callee: return jsonify({"error":"caller_id and callee_id required"}),400
        cid=str(uuid.uuid4())
        with call_lock:
            CALL_REQUESTS[cid]={"caller_id":caller,"callee_id":callee,"status":"pending"}
            CALL_SIGNALS[(int(caller),cid)]=[]; CALL_SIGNALS[(int(callee),cid)]=[]
        return jsonify({"call_id":cid}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/call/incoming/<int:callee_id>", methods=["GET"])
def get_incoming_calls(callee_id):
    try:
        with call_lock:
            p=[{"call_id":cid,**info} for cid,info in CALL_REQUESTS.items() if int(info["callee_id"])==callee_id and info["status"]=="pending"]
        return jsonify(p),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/call/response", methods=["POST"])
def call_response():
    try:
        data=request.json or {}; cid=data.get("call_id"); accept=data.get("accept")
        if not cid or accept is None: return jsonify({"error":"call_id and accept required"}),400
        with call_lock:
            req=CALL_REQUESTS.get(cid)
            if not req: return jsonify({"error":"Call not found"}),404
            req["status"]="accepted" if accept else "rejected"
            CALL_SIGNALS[(int(req["caller_id"]),cid)].append({"from":int(req["callee_id"]),"signal":{"type":"response","accept":bool(accept)}})
        return jsonify({"status":req["status"]}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/call/signal", methods=["POST"])
def call_signal():
    try:
        data=request.json or {}; cid=data.get("call_id"); fid=data.get("from"); tid=data.get("to"); sig=data.get("signal")
        if not cid or fid is None or tid is None or sig is None: return jsonify({"error":"call_id, from, to, signal required"}),400
        key=(int(tid),cid)
        with call_lock:
            if key not in CALL_SIGNALS: CALL_SIGNALS[key]=[]
            CALL_SIGNALS[key].append({"from":int(fid),"signal":sig})
        return jsonify({"ok":True}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/call/signals/<int:user_id>/<call_id>", methods=["GET"])
def get_signals(user_id, call_id):
    try:
        key=(user_id,call_id)
        with call_lock: sigs=CALL_SIGNALS.get(key,[]); CALL_SIGNALS[key]=[]
        return jsonify(sigs),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/call/end", methods=["POST"])
def call_end():
    try:
        data=request.json or {}; cid=data.get("call_id"); fid=data.get("from")
        if not cid: return jsonify({"error":"call_id required"}),400
        with call_lock:
            req=CALL_REQUESTS.get(cid)
            if not req: return jsonify({"error":"Call not found"}),404
            req["status"]="ended"
            for u in (int(req["caller_id"]),int(req["callee_id"])):
                key=(u,cid)
                if key not in CALL_SIGNALS: CALL_SIGNALS[key]=[]
                CALL_SIGNALS[key].append({"from":int(fid) if fid else None,"signal":{"type":"end"}})
        return jsonify({"ok":True}),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# SSE ENDPOINTS
# ---------------------------------------------------------------------------
@app.route("/sse/status/<int:user_id>")
def sse_status(user_id):
    global SSE_CLIENT_COUNTER
    uid=int(user_id); SSE_CLIENT_COUNTER+=1; cid=SSE_CLIENT_COUNTER; q=[]
    def gen():
        client={"closed":False,"client_id":cid,"queue":q}
        with SSE_LOCK:
            if uid not in SSE_CLIENTS: SSE_CLIENTS[uid]=[]
            SSE_CLIENTS[uid].append(client)
        try:
            yield f"event: connected\ndata: {json.dumps({'user_id':uid,'client_id':cid})}\n\n"
            lhb=time.time()
            while True:
                time.sleep(1)
                if client["closed"]: break
                if time.time()-lhb>=30: yield f"event: heartbeat\ndata: {json.dumps({'time':time.time()})}\n\n"; lhb=time.time()
                while client["queue"]: yield f"event: status_update\ndata: {json.dumps(client['queue'].pop(0))}\n\n"
        except GeneratorExit: pass
        finally:
            with SSE_LOCK:
                if uid in SSE_CLIENTS and client in SSE_CLIENTS[uid]: SSE_CLIENTS[uid].remove(client)
    return Response(gen(),mimetype='text/event-stream',headers={'Cache-Control':'no-cache','Connection':'keep-alive','X-Accel-Buffering':'no'})

@app.route("/sse/health")
def sse_health():
    with SSE_LOCK: total=sum(len(c) for c in SSE_CLIENTS.values())
    return jsonify({"active":total,"users":len(SSE_CLIENTS)})

@app.route("/sse/messages/<int:user_id>")
def sse_message_delivery(user_id):
    global MESSAGE_SSE_COUNTER
    uid=int(user_id); MESSAGE_SSE_COUNTER+=1; cid=MESSAGE_SSE_COUNTER; q=[]
    def gen():
        client={"closed":False,"client_id":cid,"queue":q}
        with MESSAGE_SSE_LOCK:
            suid=str(uid)
            if suid not in MESSAGE_SSE_CLIENTS: MESSAGE_SSE_CLIENTS[suid]=[]
            MESSAGE_SSE_CLIENTS[suid].append(client)
        try:
            yield f"event: connected\ndata: {json.dumps({'user_id':uid,'client_id':cid})}\n\n"
            lhb=time.time()
            while True:
                time.sleep(0.5)
                if client["closed"]: break
                if time.time()-lhb>=30: yield f"event: heartbeat\ndata: {json.dumps({'time':time.time()})}\n\n"; lhb=time.time()
                while client["queue"]:
                    item=client["queue"].pop(0)
                    if isinstance(item,dict): yield f"event: {item.get('event','message')}\ndata: {json.dumps(item.get('data',{}))}\n\n"
                    elif isinstance(item,str): yield item
        except GeneratorExit: pass
        finally:
            with MESSAGE_SSE_LOCK:
                suid=str(uid)
                if suid in MESSAGE_SSE_CLIENTS and client in MESSAGE_SSE_CLIENTS[suid]: MESSAGE_SSE_CLIENTS[suid].remove(client)
    return Response(gen(),mimetype='text/event-stream',headers={'Cache-Control':'no-cache','Connection':'keep-alive','X-Accel-Buffering':'no'})

# ---------------------------------------------------------------------------
# MESSAGE DELIVERY TRACKING (SSE-BASED)
# ---------------------------------------------------------------------------
@app.route("/msg/deliver", methods=["POST"])
def deliver_message():
    try:
        data=request.json or {}; cmid=data.get("client_msg_id"); sid=data.get("sender_id"); rid=data.get("receiver_id"); content=data.get("content",""); files=data.get("files",[]); rpid=data.get("reply_to_id"); cts=data.get("client_timestamp")
        if not cmid or not sid or not rid: return jsonify({"error":"client_msg_id, sender_id, receiver_id required"}),400
        smid=str(uuid.uuid4()); sts=int(time.time()*1000)
        with MESSAGE_TRACKER_LOCK: MESSAGE_TRACKER[cmid]={"client_msg_id":cmid,"server_msg_id":smid,"sender_id":int(sid),"receiver_id":int(rid),"content":content,"files":files,"reply_to_id":rpid,"client_timestamp":cts,"server_timestamp":sts,"status":"SENT"}
        execute_query("INSERT INTO messages (sender_id,receiver_id,content,reply_to_id,files,created_at) VALUES (%s,%s,%s,%s,%s,NOW())",(int(sid),int(rid),content,rpid,json.dumps(files)))
        rows=execute_query("SELECT currval(pg_get_serial_sequence('messages','id')) AS id",fetch=True)
        dbid=rows[0]["id"] if rows else None
        su=get_user_by_id(int(sid)); sun=su.get("username") if su else "Unknown"
        bp={"event":"new_message","data":{"client_msg_id":cmid,"server_msg_id":smid,"db_msg_id":dbid,"sender_id":int(sid),"sender_username":sun,"receiver_id":int(rid),"content":content,"files":files,"reply_to_id":rpid,"client_timestamp":cts,"server_timestamp":sts,"status":"SENT"}}
        _broadcast_to_sse(int(rid),"new_message",bp["data"])
        publish_to_user(str(rid),{"type":"new_message",**bp["data"]})
        execute_query("INSERT INTO unread_counts (receiver_id,sender_id,count) VALUES (%s,%s,1) ON CONFLICT (receiver_id,sender_id) DO UPDATE SET count=unread_counts.count+1",(int(rid),int(sid)),commit=True)
        _broadcast_to_sse(int(sid),"status_update",{"client_msg_id":cmid,"server_msg_id":smid,"db_msg_id":dbid,"status":"SENT","server_timestamp":sts})
        return jsonify({"client_msg_id":cmid,"server_msg_id":smid,"db_msg_id":dbid,"status":"SENT","server_timestamp":sts}),201
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/msg/status", methods=["POST"])
def update_message_status():
    try:
        data=request.json or {}; cmid=data.get("client_msg_id"); vid=data.get("viewer_id"); ns=data.get("status")
        if not cmid or not vid or not ns: return jsonify({"error":"client_msg_id, viewer_id, status required"}),400
        if ns not in ("DELIVERED","SEEN"): return jsonify({"error":"status must be DELIVERED or SEEN"}),400
        sid=None
        with MESSAGE_TRACKER_LOCK:
            e=MESSAGE_TRACKER.get(cmid)
            if e: e["status"]=ns; sid=e["sender_id"]
        if sid:
            _broadcast_to_sse(sid,"status_update",{"client_msg_id":cmid,"status":ns,"server_timestamp":int(time.time()*1000)})
            publish_to_user(str(sid),{"type":"status_update","client_msg_id":cmid,"status":ns})
        return jsonify({"ok":True,"status":ns}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/msg/fetch_missed", methods=["GET"])
def fetch_missed_messages():
    try:
        uid=request.args.get("user_id",type=int); since=request.args.get("since_timestamp",type=int)
        if not uid: return jsonify({"error":"user_id required"}),400
        q="SELECT m.id,m.sender_id,u1.username AS sender_username,m.receiver_id,u2.username AS receiver_username,m.content,m.reply_to_id,m.files,m.deleted_by_sender,m.deleted_by_receiver,m.created_at FROM messages m JOIN users u1 ON m.sender_id=u1.id JOIN users u2 ON m.receiver_id=u2.id WHERE m.receiver_id=%s AND NOT m.deleted_by_receiver"
        p=[uid]
        if since: q+=" AND EXTRACT(EPOCH FROM m.created_at)*1000>%s"; p.append(since)
        q+=" ORDER BY m.created_at ASC LIMIT 500"
        rows=execute_query(q,tuple(p),fetch=True)
        for r in rows:
            if isinstance(r.get("created_at"),datetime.datetime): r["created_at"]=r["created_at"].isoformat()
            fv=r.get("files")
            if fv is None: r["files"]=[]
            elif isinstance(fv,str):
                try: r["files"]=json.loads(fv) if isinstance(json.loads(fv),list) else []
                except: r["files"]=[]
            else: r["files"]=fv
            r["server_msg_id"]=r.get("id"); r["client_msg_id"]=None
        return jsonify({"messages":rows,"count":len(rows)}),200
    except Exception as e: return jsonify({"error":str(e)}),500

@app.route("/msg/poll_status", methods=["GET"])
def poll_message_status():
    try:
        ids_str=request.args.get("client_msg_ids","")
        if not ids_str: return jsonify({"error":"client_msg_ids required"}),400
        ids=[x.strip() for x in ids_str.split(",") if x.strip()]; res={}
        with MESSAGE_TRACKER_LOCK:
            for c in ids:
                e=MESSAGE_TRACKER.get(c)
                if e: res[c]={"status":e["status"],"server_msg_id":e.get("server_msg_id"),"server_timestamp":e.get("server_timestamp")}
                else: res[c]={"status":"UNKNOWN"}
        return jsonify({"statuses":res}),200
    except Exception as e: return jsonify({"error":str(e)}),500

# ---------------------------------------------------------------------------
# WEBRTC IN-MEMORY MSG TRACKING
# ---------------------------------------------------------------------------
@app.route("/msg/status/poll", methods=["POST"])
def poll_status():
    data=request.json or {}; mids=data.get("message_ids",[]); res={}
    with WEBRTC_LOCK:
        for m in mids:
            if m in WEBRTC_MESSAGES: res[m]={"status":WEBRTC_MESSAGES[m]["status"],"ack_received":WEBRTC_MESSAGES[m].get("ack_received",False)}
            else: res[m]={"status":"UNKNOWN"}
    return jsonify({"statuses":res,"timestamp":time.time()})

@app.route("/msg/store", methods=["POST"])
def store_message():
    data=request.json or {}; sid=data.get("sender_id"); rid=data.get("receiver_id")
    if not sid or not rid: return jsonify({"error":"sender_id and receiver_id required"}),400
    mid=data.get("message_id") or str(uuid.uuid4()); ts=time.time()
    with WEBRTC_LOCK:
        WEBRTC_MESSAGES[mid]={"id":mid,"sender_id":int(sid),"receiver_id":int(rid),"content":data.get("content",""),"msg_type":data.get("msg_type","text"),"media_url":data.get("media_url"),"status":"PENDING","ack_received":False,"timestamp":ts}
        WEBRTC_ACKS[mid]={"ack_received":False,"timestamp":ts}
    return jsonify({"msg_id":mid,"status":"stored","timestamp":ts}),201

@app.route("/msg/ack", methods=["POST"])
def receive_msg_ack():
    data=request.json or {}; mid=data.get("message_id"); rid=data.get("receiver_id")
    if not mid or not rid: return jsonify({"error":"message_id and receiver_id required"}),400
    sid=None
    with WEBRTC_LOCK:
        if mid not in WEBRTC_MESSAGES: return jsonify({"error":"Message not found"}),404
        WEBRTC_ACKS[mid]={"ack_received":True,"ack_from":int(rid),"timestamp":time.time()}
        WEBRTC_MESSAGES[mid].update({"ack_received":True,"status":"DELIVERED"}); sid=WEBRTC_MESSAGES[mid]["sender_id"]
    if sid: sse_broadcast(sid,"status_update",{"message_ids":[mid],"status":"DELIVERED","timestamp":time.time()})
    return jsonify({"msg_id":mid,"ack":True,"status":"DELIVERED"})

@app.route("/msg/deliver/<int:user_id>", methods=["GET"])
def deliver_msgs(user_id):
    since=request.args.get("since",type=float); pending=[]
    with WEBRTC_LOCK:
        for mid,msg in WEBRTC_MESSAGES.items():
            if msg["receiver_id"]!=user_id or msg["ack_received"]: continue
            if since and msg["timestamp"]<=since: continue
            pending.append({"msg_id":mid,"sender_id":msg["sender_id"],"content":msg["content"],"msg_type":msg["msg_type"],"media_url":msg.get("media_url"),"timestamp":msg["timestamp"],"status":msg["status"]})
        pending.sort(key=lambda x:x["timestamp"])
    return jsonify({"messages":pending,"count":len(pending),"timestamp":time.time()})

@app.route("/msg/deliver/ack", methods=["POST"])
def ack_delivery():
    data=request.json or {}; mids=data.get("message_ids",[]); rid=data.get("receiver_id")
    with WEBRTC_LOCK:
        for m in mids:
            if m in WEBRTC_MESSAGES and WEBRTC_MESSAGES[m]["receiver_id"]==rid:
                WEBRTC_ACKS[m]={"ack_received":True,"ack_from":int(rid),"timestamp":time.time()}
                WEBRTC_MESSAGES[m].update({"ack_received":True,"status":"DELIVERED"})
    return jsonify({"acked":mids,"count":len(mids)})

@app.route("/msg/status/<msg_id>", methods=["GET"])
def get_msg_status_route(msg_id):
    with WEBRTC_LOCK:
        if msg_id not in WEBRTC_MESSAGES: return jsonify({"error":"Not found"}),404
        m=WEBRTC_MESSAGES[msg_id]
    return jsonify({"msg_id":msg_id,"status":m["status"],"ack_received":m["ack_received"],"timestamp":m["timestamp"]})

@app.route("/msg/seen", methods=["POST"])
def mark_msg_seen():
    data=request.json or {}; mids=data.get("message_ids",[]); vid=data.get("viewer_id")
    if not mids or not vid: return jsonify({"error":"message_ids and viewer_id required"}),400
    updated=[]; su={}
    with WEBRTC_LOCK:
        for m in mids:
            if m in WEBRTC_MESSAGES:
                msg=WEBRTC_MESSAGES[m]
                if msg["receiver_id"]==vid:
                    msg.update({"status":"SEEN"}); s=msg["sender_id"]
                    su.setdefault(s,[]).append(m); updated.append(m)
    for s,ids in su.items(): sse_broadcast(s,"status_update",{"message_ids":ids,"status":"SEEN","timestamp":time.time()})
    return jsonify({"updated":updated,"count":len(updated)})

# ---------------------------------------------------------------------------
# SIGNALING (SEPARATE CHANNEL)
# ---------------------------------------------------------------------------
@app.route("/signal/msg/offer", methods=["POST"])
def signal_offer():
    d = request.json or {}
    f, t, offer = d.get("from_id"), d.get("to_id"), d.get("offer")
    ch = d.get("channel_id") or _channel_id(f, t)
    with WEBRTC_LOCK:
        k = (int(t), ch)
        WEBRTC_SIGNALS.setdefault(k, []).append({"from_id": int(f), "type": "offer", "data": offer, "timestamp": time.time(), "channel_id": ch})
    return jsonify({"channel_id": ch, "stored": True}), 201

@app.route("/signal/msg/answer", methods=["POST"])
def signal_answer():
    d = request.json or {}
    f, t, ans, ch = d.get("from_id"), d.get("to_id"), d.get("answer"), d.get("channel_id")
    with WEBRTC_LOCK:
        k = (int(t), ch)
        WEBRTC_SIGNALS.setdefault(k, []).append({"from_id": int(f), "type": "answer", "data": ans, "timestamp": time.time(), "channel_id": ch})
    return jsonify({"stored": True}), 201

@app.route("/signal/msg/ice", methods=["POST"])
def signal_ice():
    d = request.json or {}
    f, t, cand, ch = d.get("from_id"), d.get("to_id"), d.get("candidate"), d.get("channel_id")
    with WEBRTC_LOCK:
        k = (int(t), ch)
        WEBRTC_SIGNALS.setdefault(k, []).append({"from_id": int(f), "type": "ice", "data": cand, "timestamp": time.time(), "channel_id": ch})
    return jsonify({"stored": True}), 201

@app.route("/signal/msg/<int:user_id>", methods=["GET"])
def poll_signals(user_id):
    ch = request.args.get("channel_id")
    since = request.args.get("since", type=float)
    signals = []
    with WEBRTC_LOCK:
        for k, sigs in WEBRTC_SIGNALS.items():
            if k[0] != user_id: continue
            if ch and k[1] != ch: continue
            signals.extend([s for s in sigs if not since or s["timestamp"] > since])
    signals.sort(key=lambda x: x["timestamp"])
    return jsonify({"signals": signals, "count": len(signals), "timestamp": time.time()})

@app.route("/signal/msg/clear", methods=["POST"])
def clear_signals():
    d = request.json or {}
    uid, ch = d.get("user_id"), d.get("channel_id")
    ts = d.get("before_timestamp")
    with WEBRTC_LOCK:
        k = (int(uid), ch)
        if k in WEBRTC_SIGNALS:
            WEBRTC_SIGNALS[k] = [s for s in WEBRTC_SIGNALS[k] if not ts or s["timestamp"] > ts] if ts else []
    return jsonify({"cleared": len(WEBRTC_SIGNALS.get(k, []))})

# ---------------------------------------------------------------------------
# USER PRESENCE
# ---------------------------------------------------------------------------
@app.route("/users/heartbeat", methods=["POST"])
def heartbeat():
    d = request.json or {}
    uid, sid = int(d.get("user_id")), d.get("session_id") or str(uuid.uuid4())
    with WEBRTC_LOCK:
        WEBRTC_ONLINE[uid] = {"last_seen": time.time(), "session_id": sid, "online": True}
    return jsonify({"user_id": uid, "online": True, "session_id": sid})

@app.route("/users/<int:user_id>/online", methods=["GET"])
def check_online(user_id):
    with WEBRTC_LOCK:
        data = WEBRTC_ONLINE.get(user_id, {})
        online = (time.time() - data.get("last_seen", 0)) < 60 if data else False
    return jsonify({"user_id": user_id, "online": online, "last_seen": data.get("last_seen") if data else None})

@app.route("/users/online/batch", methods=["POST"])
def batch_online():
    uids = request.json or {}
    results = {}
    with WEBRTC_LOCK:
        for uid in uids.get("user_ids", []):
            uid = int(uid)
            data = WEBRTC_ONLINE.get(uid, {})
            results[uid] = {"online": (time.time() - data.get("last_seen", 0)) < 60 if data else False}
    return jsonify({"users": results, "timestamp": time.time()})

# ---------------------------------------------------------------------------
# WEBRTC REAL-TIME MESSAGING SYSTEM
# ---------------------------------------------------------------------------
@app.route("/webrtc/online", methods=["POST"])
def webrtc_online():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    socket_id = data.get("socket_id")
    webrtc = data.get("webrtc", False)
    _set_user_online(user_id, socket_id, webrtc)
    return jsonify({"status": "online", "timestamp": time.time()})

@app.route("/webrtc/offline", methods=["POST"])
def webrtc_offline():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    _set_user_offline(user_id)
    return jsonify({"status": "offline"})

@app.route("/webrtc/heartbeat", methods=["POST"])
def webrtc_heartbeat():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    _process_heartbeat(user_id)
    return jsonify({"status": "ok", "timestamp": time.time()})

@app.route("/webrtc/status/<int:target_user_id>", methods=["GET"])
def webrtc_check_status(target_user_id):
    is_online = _is_user_online(target_user_id)
    return jsonify({"user_id": target_user_id, "online": is_online, "status": _get_user_status(target_user_id)})

@app.route("/webrtc/status/batch", methods=["POST"])
def webrtc_batch_status():
    user_ids = request.json or {}
    user_ids = user_ids.get("user_ids", [])
    status = _get_batch_status(user_ids)
    return jsonify({"users": status})

@app.route("/webrtc/message", methods=["POST"])
def webrtc_send_message():
    sender_id = get_auth_user_id()
    if not sender_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    receiver_id = data.get("receiver_id")
    content = data.get("content", "")
    client_message_id = data.get("client_message_id") or str(uuid.uuid4())
    client_timestamp = data.get("client_timestamp", time.time())
    files = data.get("files", [])
    if not receiver_id: return jsonify({"error": "receiver_id required"}), 400
    server_message_id = str(uuid.uuid4())
    server_timestamp = datetime.datetime.now(datetime.timezone.utc)
    receiver_online = _is_user_online(receiver_id)
    try:
        existing = execute_query("SELECT id, server_message_id FROM webrtc_messages WHERE client_message_id = %s",(client_message_id,),fetch=True)
        if existing:
            return jsonify({"server_message_id": existing[0]["server_message_id"], "client_message_id": client_message_id, "sender_id": sender_id, "receiver_id": receiver_id, "content": content, "client_timestamp": client_timestamp, "server_timestamp": server_timestamp.isoformat(), "files": files or [], "status": "existing", "receiver_online": receiver_online, "delivery_method": "webrtc" if receiver_online else "websocket", "duplicate": True}), 200
        execute_query("""INSERT INTO webrtc_messages (server_message_id, client_message_id, sender_id, receiver_id, content, client_timestamp, server_timestamp, files, status, created_at) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s) ON CONFLICT (client_message_id) DO NOTHING""",(server_message_id, client_message_id, sender_id, receiver_id, content, client_timestamp, server_timestamp, json.dumps(files or []), MSG_PENDING, server_timestamp),commit=True)
    except Exception as e:
        app.logger.error(f"Failed to create message: {e}")
        return jsonify({"error": "Failed to create message"}), 500
    conv_id = f"{min(sender_id, receiver_id)}_{max(sender_id, receiver_id)}"
    message_payload = {"t": "msg", "conv": conv_id, "id": server_message_id, "cid": client_message_id, "sid": sender_id, "rid": receiver_id, "content": content, "cts": client_timestamp, "sts": server_timestamp.isoformat(), "files": files or []}
    ws_delivered = False
    try:
        publish_to_user(str(receiver_id), message_payload)
        ws_delivered = True
    except: pass
    if not ws_delivered:
        try: sse_broadcast(receiver_id, "msg", message_payload)
        except: pass
    if ws_delivered:
        try: publish_to_user(str(sender_id), {"type": "delivered", "client_message_id": client_message_id, "server_message_id": server_message_id, "receiver_id": receiver_id})
        except: pass
    try: publish_to_user(str(sender_id), {"type": "message_sent", "client_message_id": client_message_id, "server_message_id": server_message_id, "receiver_online": receiver_online, "delivery_method": "webrtc" if receiver_online else "websocket"})
    except: pass
    return jsonify({"server_message_id": server_message_id, "client_message_id": client_message_id, "sender_id": sender_id, "receiver_id": receiver_id, "content": content, "client_timestamp": client_timestamp, "server_timestamp": server_timestamp.isoformat(), "files": files or [], "status": MSG_PENDING, "receiver_online": receiver_online, "delivery_method": "webrtc" if receiver_online else "websocket"}), 201

@app.route("/webrtc/message/ack", methods=["POST"])
def webrtc_message_ack():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    client_message_id = data.get("client_message_id")
    status = data.get("status")
    if not client_message_id or not status: return jsonify({"error": "client_message_id and status required"}), 400
    try:
        msg = execute_query("SELECT sender_id FROM webrtc_messages WHERE client_message_id = %s",(client_message_id,),fetch=True)
        sender_id = msg[0]["sender_id"] if msg else None
        execute_query("UPDATE webrtc_messages SET status = %s WHERE client_message_id = %s",(status, client_message_id),commit=True)
        if sender_id:
            try: publish_to_user(str(sender_id), {"type": "status", "client_message_id": client_message_id, "status": status})
            except: pass
    except Exception as e:
        app.logger.error(f"ACK failed: {e}")
        return jsonify({"error": "Failed to update status"}), 500
    return jsonify({"success": True})

@app.route("/webrtc/messages/pending", methods=["GET"])
def webrtc_get_pending():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    try:
        messages = execute_query("""SELECT id, client_id, receiver_id, content, status, version, server_timestamp FROM messages WHERE sender_id = %s AND status != 'seen' ORDER BY id DESC LIMIT 50""",(user_id,),fetch=True)
        return jsonify({"messages": messages or []}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/webrtc/retry_delivery", methods=["POST"])
def webrtc_retry_delivery():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    message_ids = data.get("message_ids", [])
    if not message_ids: return jsonify({"error": "message_ids required"}), 400
    try:
        resend_count = 0
        for msg_id in message_ids:
            msg = execute_query("SELECT * FROM messages WHERE id = %s AND sender_id = %s",(msg_id, user_id),fetch=True)
            if msg:
                payload = {"t": "msg", "id": msg[0]["id"], "cid": msg[0]["client_id"], "sid": msg[0]["sender_id"], "rid": msg[0]["receiver_id"], "content": msg[0]["content"], "files": msg[0].get("files"), "sts": msg[0]["server_timestamp"].isoformat() if msg[0].get("server_timestamp") else None}
                try:
                    publish_to_user(str(msg[0]["receiver_id"]), payload)
                    resend_count += 1
                except: pass
        return jsonify({"resent": resend_count}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/webrtc/ack_delivery", methods=["POST"])
def webrtc_ack_delivery():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    client_id = data.get("client_id")
    conv = data.get("conv")
    ldid = data.get("ldid")
    if not client_id and (not ldid or not conv): return jsonify({"error": "client_id or (ldid+conv) required"}), 400
    try:
        if ldid and conv:
            parts = conv.split("_")
            if len(parts) == 2:
                sid, rid = int(parts[0]), int(parts[1])
                receiver = sid if rid == user_id else rid
                updated = execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE receiver_id=%s AND sender_id=%s AND id<=%s AND version<2 RETURNING id",(receiver, user_id, ldid),commit=True)
                if updated:
                    publish_to_user(str(receiver), {"t":"delivered","conv":conv,"ldid":ldid,"v":2,"src":"server","via":"http"})
        if client_id:
            msg = execute_query("SELECT sender_id FROM messages WHERE client_id = %s",(client_id,),fetch=True)
            if not msg: return jsonify({"error": "Message not found"}), 404
            sender_id = msg[0]["sender_id"]
            updated = execute_query("UPDATE messages SET status='delivered',version=2,status_updated_at=NOW() WHERE client_id=%s AND version<2 RETURNING id",(client_id,),commit=True)
            if updated:
                publish_to_user(str(sender_id), {"t":"delivered","cid":client_id,"v":2,"src":"server","via":"http"})
        return jsonify({"success": True}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/webrtc/ack_seen", methods=["POST"])
def webrtc_ack_seen():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    other_id = data.get("other_id")
    last_seen_id = data.get("last_seen_id")
    if not other_id or not last_seen_id: return jsonify({"error": "other_id and last_seen_id required"}), 400
    try:
        execute_query("UPDATE messages SET status='seen',version=3,status_updated_at=NOW() WHERE sender_id=%s AND receiver_id=%s AND id<=%s AND version<3",(other_id, user_id, last_seen_id),commit=True)
        execute_query("DELETE FROM unread_counts WHERE receiver_id=%s AND sender_id=%s",(user_id, other_id),commit=True)
        publish_to_user(str(other_id), {"t":"seen","conv":f"{min(other_id,user_id)}_{max(other_id,user_id)}","lsid":last_seen_id,"src":"server","via":"http"})
        return jsonify({"success": True}), 200
    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route("/webrtc/messages/<int:other_user_id>", methods=["GET"])
def webrtc_get_conversation(other_user_id):
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    try:
        rows = execute_query("""SELECT server_message_id, client_message_id, sender_id, receiver_id, content, client_timestamp, server_timestamp, files, status FROM webrtc_messages WHERE (sender_id=%s AND receiver_id=%s) OR (sender_id=%s AND receiver_id=%s) ORDER BY server_timestamp ASC""",(user_id, other_user_id, other_user_id, user_id),fetch=True)
        return jsonify({"messages": rows or []})
    except: return jsonify({"messages": []})

@app.route("/webrtc/signal/offer", methods=["POST"])
def webrtc_signal_offer():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    to_id = data.get("to_id")
    offer = data.get("offer")
    channel_id = data.get("channel_id") or f"{user_id}_{to_id}"
    with WEBRTC_LOCK:
        k = (int(to_id), channel_id)
        WEBRTC_SIGNALS.setdefault(k, []).append({"from_id": user_id, "type": "offer", "data": offer, "timestamp": time.time()})
    return jsonify({"channel_id": channel_id, "stored": True})

@app.route("/webrtc/signal/answer", methods=["POST"])
def webrtc_signal_answer():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    to_id = data.get("to_id")
    answer = data.get("answer")
    channel_id = data.get("channel_id")
    with WEBRTC_LOCK:
        k = (int(to_id), channel_id)
        WEBRTC_SIGNALS.setdefault(k, []).append({"from_id": user_id, "type": "answer", "data": answer, "timestamp": time.time()})
    return jsonify({"stored": True})

@app.route("/webrtc/signal/ice", methods=["POST"])
def webrtc_signal_ice():
    user_id = get_auth_user_id()
    if not user_id: return jsonify({"error": "unauthorized"}), 401
    data = request.json or {}
    to_id = data.get("to_id")
    candidate = data.get("candidate")
    channel_id = data.get("channel_id")
    with WEBRTC_LOCK:
        k = (int(to_id), channel_id)
        WEBRTC_SIGNALS.setdefault(k, []).append({"from_id": user_id, "type": "ice", "data": candidate, "timestamp": time.time()})
    return jsonify({"stored": True})

@app.route("/webrtc/signal/<int:target_user_id>", methods=["GET"])
def webrtc_get_signals(target_user_id):
    channel_id = request.args.get("channel_id")
    with WEBRTC_LOCK:
        k = (target_user_id, channel_id)
        signals = WEBRTC_SIGNALS.get(k, [])
        WEBRTC_SIGNALS[k] = []
    return jsonify({"signals": signals})

# ---------------------------------------------------------------------------
# STARTUP: ensure all tables exist
# ---------------------------------------------------------------------------
ensure_push_tokens_table()
ensure_unread_table()
ensure_webrtc_messages_table()
