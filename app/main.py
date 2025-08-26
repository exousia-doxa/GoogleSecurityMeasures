# main.py
import logging
import os
import re
import json
import base64
import string
import random
import hashlib
import quopri
import time
from datetime import datetime, timedelta, timezone
from html import unescape
from email.mime.text import MIMEText
import sys
from googleapiclient.discovery import build
from jinja2 import Environment, FileSystemLoader, select_autoescape
from google.oauth2 import service_account
import google.auth.transport.requests

CONFIG_PATH = "config.json"
if not os.path.exists(CONFIG_PATH):
    raise FileNotFoundError(f"Config file not found: {CONFIG_PATH}")
with open(CONFIG_PATH, "r", encoding="utf-8") as cf:
    CONFIG = json.load(cf)

SERVICE_ACCOUNT_FILE = CONFIG["SERVICE_ACCOUNT_FILE"]
HANDLER_USER = CONFIG["HANDLER_USER"]
ADMIN_USER = CONFIG["ADMIN_USER"]
LOG_FILE = CONFIG.get("LOG_FILE", "alerts_log.json")
ORG_UNIT_TEAM_LEADER_ROLE_ID = CONFIG["ORG_UNIT_TEAM_LEADER_ROLE_ID"]
ALERT_SENDER_EMAIL = CONFIG.get("ALERT_SENDER_EMAIL", "google-workspace-alerts-noreply@google.com")
TEMPLATE_DIR = CONFIG.get("TEMPLATE_DIR", "templates")
SCOPES = CONFIG.get("SCOPES", [])

STATUS_SUSPENDED = "suspended"
STATUS_ACCEPTED = "accepted"
STATUS_DECLINED = "declined"

env = Environment(loader=FileSystemLoader(TEMPLATE_DIR), autoescape=select_autoescape(["html", "xml"]))

# Ця функція робить HTTP-запити через передану сесію (AuthorizedSession) з підтримкою пагінації та повторних спроб.
# Переважно використовується для викликів Google Admin API: вона збирає сторінки відповіді (nextPageToken),
# повертає список JSON-відповідей і логірує/завершує виконання при помилці або при перевищенні таймауту.
def create_session(max_time, session, type, url, json=None, params=None, query_type=""):
    timer = 2
    response = None
    page_token = None
    data = []
    url += f"{query_type}"

    while True:
        local_url = url
        if page_token:
            local_url += f"&pageToken={page_token}"
        if type == "fetch":
            response = session.request(url=local_url, method='fetch', json=json, params=params)
        elif type == "post":
            response = session.request(url=local_url, method='post', json=json, params=params)
        elif type == "patch":
            response = session.request(url=local_url, method='patch', json=json, params=params)
        elif type == "delete":
            response = session.request(url=local_url, method='delete', json=json, params=params)
        elif type == "get":
            response = session.request(url=local_url, method='get', json=json, params=params)

        data.append(response.json())

        page_token = data[-1].get('nextPageToken')

        try:
            if response.status_code == 200 and not page_token:
                return data
            elif page_token:
                continue
            elif timer < max_time:
                time.sleep(timer)
                timer *= timer
            else:
                log(f"Request error | type: {type}, url: {url}, response: {response}. Error: {str(e)}")
                sys.exit(1)
        except Exception as e:
            log(f"Request error | type: {type}, url: {url}, response: {response}. Error: {str(e)}")
            sys.exit(1)

logging.basicConfig(filename='main.log', level=logging.ERROR)

#Проста обгортка для логування: записує повідомлення у файл логів (main.log) через logging та одночасно
# виводить його на консоль з міткою часу. Використовується скрізь для централізованого ведення подій і помилок.
def log(message):
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    logging.error(f"{timestamp} - {message}")
    print(f"{timestamp} - {message}")

# Завантажує локальний JSON-файл з історією сповіщень (LOG_FILE) у пам’ять як словник. Якщо файл відсутній —
# повертає пустий словник; при проблемі з читанням робить бекап і теж повертає пусту структуру.
def load_alert_log():
    if not os.path.exists(LOG_FILE):
        return {}
    with open(LOG_FILE, "r", encoding="utf-8") as f:
        try:
            return json.load(f)
        except Exception:
            backup = LOG_FILE + ".bak"
            try:
                os.replace(LOG_FILE, backup)
            except Exception:
                pass
            return {}

# Атомарно зберігає словник логів у LOG_FILE: записує у тимчасовий файл і замінює основний файл.
# Гарантує цілісність файлу при записі.
def save_alert_log(log):
    tmp = LOG_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(log, f, indent=2, ensure_ascii=False)
    os.replace(tmp, LOG_FILE)

# Обрізає запис у логах, залишаючи тільки записи молодші за вказану кількість днів (за замовчуванням 7).
# Перевіряє fetched_at у кожному записі і відкидає некоректні або старі записи.
def prune_alert_log(log, days=7):
    cutoff = datetime.now(timezone.utc) - timedelta(days=days)
    new = {}
    for k, v in log.items():
        fetched_at = v.get("fetched_at")
        if not fetched_at:
            continue
        try:
            dt = datetime.fromisoformat(fetched_at)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            if dt > cutoff:
                new[k] = v
        except Exception:
            continue
    return new

# Перевіряє, чи знаходиться шлях організаційної одиниці користувача під вказаним шляхом OU (наприклад "/A/B" під "/A").
# Нормалізує слеші і пробіли та повертає булеве значення — використовується для визначення відповідних тімлідів по ієрархії.
def is_under(user_ou: str, ou_path: str) -> bool:
    def norm(p: str) -> str:
        return p.strip().rstrip('/')

    u = norm(user_ou or '')
    o = norm(ou_path or '')

    if u == o:
        return True
    return u.startswith(o + '/')

# Генерує унікальний хеш (sha256) для сповіщення на основі email користувача, IP та дати/часу.
# Використовується як ідентифікатор запису в alert_log і як значення, яке відправляється тімліду для підтвердження/відхилення.
def generate_hash(user_email, ip, date):
    base = f"{user_email}__{ip}__{date}"
    return hashlib.sha256(base.encode("utf-8")).hexdigest()

# ========= EMAIL TEMPLATES & SENDING ========= #
# Рендерить HTML-лист через Jinja2-шаблон (email_template.html) з переданими параметрами
# (title, body, footer, action_block). Повертає готовий HTML-контент для надсилання.
def render_email_template(title, body, footer=None, action_block=None):
    template = env.get_template("email_template.html")
    html = template.render(
        title=title,
        body=body,
        footer=footer,
        action_block=action_block,
        year=datetime.now(timezone.utc).year
    )
    return html

# Формує HTML-блок з інформацією по сповіщенню (користувач, IP, дата/час) у зручному для вставки в листі вигляді.
# Допоміжна функція для уніфікованого футеру.
def make_alert_footer(alert_info):
    return (
        f"Користувач: <b>{alert_info['user']}</b><br>"
        f"IP-адреса: <b>{alert_info['ip']}</b><br>"
        f"Дата/час: <b>{alert_info['date']}</b>"
    )

# Надсилає готовий MIME-повідомлення через Gmail API: кодує у base64-url і викликає users.messages.send.
# При помилці логірує подію з subject листа.
def send_gmail(gmail_svc, msg_obj):
    try:
        raw = base64.urlsafe_b64encode(msg_obj.as_bytes()).decode()
        gmail_svc.users().messages().send(userId="me", body={"raw": raw}).execute()
    except Exception as e:
        log({"event": "gmail_send_error", "error": str(e), "subject": msg_obj.get("subject")})

# Готує і відсилає тімліду повідомлення про підозрілий вхід із двома кнопками (mailto-посиланнями) для підтвердження
# або відхилення входу. Формує HTML через render_email_template, вкладає унікальний хеш у тіло посилання і логірує відправку.
def send_team_leader_alert(gmail_svc, to_address, alert_info, unique_hash):
    body_content = (
        "Повідомляємо, що служба безпеки Google Workspace зафіксувала "
        "підозрілу спробу входу до облікового запису, "
        "яка не відповідає типовим шаблонам поведінки користувача.<br><br>"
        "<b>На даний момент обліковий запис заблоковано:</b><br>"
        "- Якщо користувач, здійснював цей вхід, або знаходився у відповідному місці/часі, блокування буде знято.<br>"
        "- Якщо користувач не підтверджує вхід - доступ до облікового запису буде змінено та надіслано Вам зворотнім листом.<br><br>"
        "<b>Натисність на відповідну опцію меню та надішліть зворотній лист без змін!</b>"
    )
    footer = make_alert_footer(alert_info)
    accept_subject = "Accept: Suspicious login"
    decline_subject = "Decline: Suspicious login"
    mailto_body = unique_hash
    accept_url = f"mailto:{HANDLER_USER}?subject={accept_subject}&body={mailto_body}"
    decline_url = f"mailto:{HANDLER_USER}?subject={decline_subject}&body={mailto_body}"

    action_block = (
        f'<a href="{accept_url}" style="'
        "background:#b3eecb;"
        "color:#175436;"
        "padding:11px 33px;"
        "text-decoration:none;"
        "border-radius:5px;"
        "font-size:15px;"
        "font-weight:500;"
        "letter-spacing:0.01em;"
        "box-shadow:0 1.5px 6px rgba(60,64,67,0.08);"
        "display:inline-block;"
        "margin-right:18px;"
        "border:1px solid #75db8f;"
        '">Вхід підтверджую</a>'
        f'<a href="{decline_url}" style="'
        "background:#ffd3d6;"
        "color:#900c17;"
        "padding:11px 30px;"
        "text-decoration:none;"
        "border-radius:5px;"
        "font-size:15px;"
        "font-weight:500;"
        "letter-spacing:0.01em;"
        "box-shadow:0 1.5px 6px rgba(60,64,67,0.08);"
        "display:inline-block;"
        "border:1px solid #ffa3a3;"
        '">Вхід не підтверджую</a>'
    )

    html_body = render_email_template(
        title="Підозріла спроба входу",
        body=body_content,
        footer=footer,
        action_block=action_block
    )
    msg = MIMEText(html_body, "html")
    msg["to"] = to_address
    msg["subject"] = "Suspicious Login Alert – Action Required"
    send_gmail(gmail_svc, msg)
    log({"event": "alert_email_sent", "to": to_address, "user": alert_info["user"], "hash": unique_hash})

# Надсилає тімлідам повідомлення про результат обробки (accept або decline). У випадку decline включає новий пароль.
# Використовується після того, як адміністратор розблокував обліковий запис та, за потреби, змінив пароль.
def send_team_leader_notification(gmail_svc, to_address, alert_info, action, new_password=None):
    footer = make_alert_footer(alert_info)
    if action == "accept":
        title = "Обліковий запис відновлено"
        body = "Обліковий запис було успішно відновлено.<br>"
    else:
        title = "Обліковий запис відновлено"
        body = (
            "Обліковий запис було успішно відновлено.<br><br>"
            f"Увага! З метою безпеки змінено пароль користувача.<br>Новий пароль: <b>{new_password}</b><br>"
        )

    html_body = render_email_template(
        title=title,
        body=body,
        footer=footer,
        action_block=None
    )
    subj = "Suspicious Login Alert - Account Restored"
    msg = MIMEText(html_body, "html")
    msg["to"] = to_address
    msg["subject"] = subj
    send_gmail(gmail_svc, msg)
    log({"event": "account_notification_sent", "to": to_address, "user": alert_info["user"], "action": action})

########################################################################################################################

# Отримує перелік повідомлень (ids) з Gmail за вказаним запитом q, обробляючи пагінацію.
# Повертає список знайдених повідомлень (часто лише id та threadId).
def list_messages(gmail_svc, q):
    results = []
    page_token = None
    while True:
        try:
            resp = gmail_svc.users().messages().list(userId="me", q=q, pageToken=page_token).execute()
        except Exception as e:
            log({"event": "gmail_list_error", "query": q, "error": str(e)})
            break
        results.extend(resp.get("messages", []))
        page_token = resp.get("nextPageToken")
        if not page_token:
            break
    return results

# Побудова запиту для пошуку листів від певної адреси з шаблоном у темі/тексті за останні 7 днів.
# Викликає list_messages для виконання запиту і повертає результати.
def search_mail(gmail_service, pattern, email):
    after_ts = int((datetime.now(timezone.utc) - timedelta(days=7)).timestamp())
    q = f'from:{email} {pattern} after:{after_ts}'
    return list_messages(gmail_service, q)

# Витягує та декодує тіло листа з повної структури повідомлення Gmail: підтримує multipart/parts, base64/url-safe,
# quoted-printable, text/plain та text/html; робить очищення HTML у текст і повертає очищений текстовий вміст або None при невдачі.
def extract_content(msg_detail):
    payload = msg_detail.get("payload", {})
    data = None
    mime_type = None
    headers = []

    parts = payload.get("parts")
    if parts:
        plain_part = next((p for p in parts if p.get("mimeType") == "text/plain"), None)
        html_part = next((p for p in parts if p.get("mimeType") == "text/html"), None)
        part = plain_part or html_part
        mime_type = part.get("mimeType") if part else None
        data = part.get("body", {}).get("data") if part else None
        headers = part.get("headers", []) if part else []
    else:
        mime_type = payload.get("mimeType")
        data = payload.get("body", {}).get("data")
        headers = payload.get("headers", [])

    if not data:
        return None

    s = data
    if isinstance(s, str):
        s += "=" * (-len(s) % 4)
        try:
            raw = base64.urlsafe_b64decode(s.encode("utf-8"))
        except Exception:
            try:
                raw = base64.b64decode(s.encode("utf-8"))
            except Exception:
                return None
    else:
        try:
            raw = base64.urlsafe_b64decode(data)
        except Exception:
            try:
                raw = base64.b64decode(data)
            except Exception:
                return None

    cte_header = next((h["value"].lower() for h in headers if h["name"].lower() == "content-transfer-encoding"), "")
    if "quoted-printable" in cte_header:
        try:
            decoded = quopri.decodestring(raw).decode("utf-8", errors="replace")
        except Exception:
            decoded = raw.decode("utf-8", errors="replace")
    else:
        decoded = raw.decode("utf-8", errors="replace")

    if mime_type == "text/html":
        txt = re.sub(r'<[^>]+>', '', decoded)
        txt = unescape(txt)
        txt = txt.replace('=20', ' ').replace('\r\n', '\n')
        lines = [l.strip() for l in re.split(r'<br\s*/?>|\n', txt) if l.strip()]
        txt = "\n".join(lines)
        return txt

    decoded = decoded.replace('=20', ' ')
    decoded = decoded.replace('=\r\n', '').replace('=\n', '')
    return decoded

########################################################################################################################

# Викликає Admin SDK для призупинення користувача (suspended=True).
# Логірує успіх або помилку і повертає булевий результат операції.
def suspend_user(admin_session, user_email):
    try:
        admin_session.users().update(userKey=user_email, body={"suspended": True}).execute()
        log({"event": "suspend_user", "user": user_email})
        return True
    except Exception as e:
        log({"event": "suspend_user_error", "user": user_email, "error": str(e)})
        return False

# Викликає Admin SDK для зняття призупинення з користувача (suspended=False).
# Логірує результат і повертає булеве значення успіху.
def unblock_user(admin_session, user_email):
    try:
        admin_session.users().update(userKey=user_email, body={"suspended": False}).execute()
        log({"event": "unsuspend_user", "user": user_email})
        return True
    except Exception as e:
        log({"event": "unsuspend_user_error", "user": user_email, "error": str(e)})
        return False

# Генерує криптографічно більш-менш надійний випадковий пароль заданої довжини (за замовчуванням 20) з літер та цифр,
# використовуючи SystemRandom.
def generate_password(length=20):
    characters = string.ascii_letters + string.digits
    return ''.join(random.SystemRandom().choice(characters) for _ in range(length))

# Встановлює новий пароль для користувача через Admin SDK і примушує змінити пароль при наступному вході
# (changePasswordAtNextLogin=True). Повертає згенерований пароль або None при помилці, а також логірує подію.
def set_password(admin_session, user_email):
    password = generate_password()
    try:
        admin_session.users().update(
            userKey=user_email,
            body={"password": password, "changePasswordAtNextLogin": True}
        ).execute()
        log({"event": "set_new_password", "user": user_email})
        return password
    except Exception as e:
        log({"event": "set_new_password_error", "user": user_email, "error": str(e)})
        return None

########################################################################################################################

# Обробляє відповіді HANDLER_USER на листи з результатом ("Accept: Suspicious login" / "Decline: Suspicious login").
# Валідовує відправника та хеш у тілі листа, оновлює alert_log (status/actioned_at), знімає призупинення, у випадку decline —
# змінює пароль, та надсилає тімлідам повідомлення про результат. Логірує всі ключові кроки.
def process_action_responses(gmail_session, admin_session, alert_log):
    for message in search_mail(gmail_session, '(subject:"Accept: Suspicious login" OR subject:"Decline: Suspicious login")', HANDLER_USER):
        message_id = message.get("id")
        message_detail = gmail_session.users().messages().get(userId="me", id=message_id, format="full").execute()

        message_header = message_detail.get("payload", {}).get("headers", [])
        message_subject_header = next((h["value"] for h in message_header if h["name"].lower() == "subject"), "")
        message_from_header = next((h["value"] for h in message_header if h["name"].lower() == "from"), "")
        message_body = extract_content(message_detail)
        del message_detail

        hash_value = message_body.strip()
        if not re.fullmatch(r"[0-9a-f]{64}", hash_value):
            continue

        from_email = None
        if message_from_header:
            match = re.search(r'<(.+?)>', message_from_header)
            from_email = match.group(1) if match else message_from_header.strip()

        if from_email != HANDLER_USER:
            log({"event": "invalid_response_sender", "from": from_email, "expected": HANDLER_USER, "hash": hash_value})
            continue
        del from_email

        alert = alert_log.get(hash_value)
        if not alert or alert.get("status") != STATUS_SUSPENDED:
            continue

        alert_info = {
            "user": alert['user'],
            "ip": alert['ip'],
            "date": alert['date'],
            "message_id": alert.get("message_id")
        }

        if "accept" in message_subject_header.lower():
            alert["status"] = STATUS_ACCEPTED
            alert["actioned_at"] = datetime.now(timezone.utc).isoformat()
            if unblock_user(admin_session, alert['user']):
                save_alert_log(alert_log)
            else:
                alert["status"] = STATUS_SUSPENDED
            for tl in alert.get("team_leaders", []):
                send_team_leader_notification(gmail_session, tl, alert_info, action="accept")
            log({"event": "processed_accept", "hash": hash_value, "user": alert['user']})
        elif "decline" in message_subject_header.lower():
            alert["status"] = STATUS_DECLINED
            alert["actioned_at"] = datetime.now(timezone.utc).isoformat()
            if unblock_user(admin_session, alert['user']):
                new_password = set_password(admin_session, alert['user'])
                save_alert_log(alert_log)
            else:
                alert["status"] = STATUS_SUSPENDED
                new_password = None
            for tl in alert.get("team_leaders", []):
                send_team_leader_notification(gmail_session, tl, alert_info, action="decline", new_password=new_password)
            log({"event": "processed_decline", "hash": hash_value, "user": alert['user']})

# Шукає нові вхідні сповіщення від ALERT_SENDER_EMAIL ("Alert: Suspicious login"), парсить потрібні поля
# (User, Attempted Login IP, Activity Date), генерує унікальний хеш, призупиняє обліковий запис користувача,
# визначає відповідних тімлідів за OU і надсилає їм початкове сповіщення з кнопками. Записує новий запис у alert_log
# з інформацією про сповіщення і статусом suspended.
def process_alert_requests(gmail_session, admin_session, users_list, team_leader_members, alert_log):
    new_alerts = []

    for message in search_mail(gmail_session, 'subject:"Alert: Suspicious login"', ALERT_SENDER_EMAIL):
        message_id = message.get("id")
        message_detail = gmail_session.users().messages().get(userId="me", id=message_id, format="full").execute()

        message_header = message_detail.get("payload", {}).get("headers", [])
        message_from_header = next((h["value"] for h in message_header if h["name"].lower() == "from"), "")
        message_subject_header = next((h["value"] for h in message_header if h["name"].lower() == "subject"), "")
        message_from_header = next((h["value"] for h in message_header if h["name"].lower() == "from"), "")
        message_body = extract_content(message_detail)
        del message_detail

        from_email = None
        if message_from_header:
            match = re.search(r'<(.+?)>', message_from_header)
            from_email = match.group(1) if match else message_from_header.strip()

        if from_email != ALERT_SENDER_EMAIL:
            log({"event": "invalid_alert_sender", "from": from_email, "expected": ALERT_SENDER_EMAIL})
            continue
        del from_email

        parts = [p.strip() for p in message_body.replace("=\n", "").split('\n') if p.strip()]
        def extract_field(line):
            if "User:" in line:
                return 'user', line.split("User:")[1].strip()
            if "Attempted Login IP:" in line:
                return 'ip', line.split("Attempted Login IP:")[1].strip()
            if "Activity Date:" in line:
                return 'date', line.split("Activity Date:")[1].strip()
            return None, None

        temp_data = {}
        for l in parts:
            k, v = extract_field(l)
            if k:
                temp_data[k] = v

        user_email = temp_data.get('user')
        user_ip = temp_data.get('ip')
        user_date = temp_data.get('date')
        if not (user_email and user_ip and user_date):
            log({"event": "alert_parse_failed", "msg_id": message_id, "extracted": temp_data})
            continue

        unique_hash = generate_hash(user_email, user_ip, user_date)
        if unique_hash in alert_log:
            continue

        user_ou = [user.get("orgUnitPath") for user in users_list if user.get("primaryEmail") == user_email][0]
        alert_team_leads = []

        alert_info = {
            "user": user_email,
            "ip": user_ip,
            "date": user_date,
            "message_id": message_id
        }

        suspended = suspend_user(admin_session, user_email)

        for team_leader in team_leader_members:
            team_leader_data = [user for user in users_list if user.get("id") == team_leader][0]
            if not team_leader_data:
                continue
            team_leader_email = team_leader_data.get("primaryEmail")
            team_leader_ou = team_leader_data.get("orgUnitPath")
            if team_leader_ou and is_under(user_ou, team_leader_ou) and team_leader_email != user_email:
                send_team_leader_alert(gmail_session, team_leader_email, alert_info, unique_hash)
                alert_team_leads.append(team_leader_email)

        alert_record = {
            **alert_info,
            "team_leaders": alert_team_leads,
            "unique_hash": unique_hash,
            "suspended": bool(suspended)
        }

        alert_log[unique_hash] = {"fetched_at": datetime.now(timezone.utc).isoformat(), **alert_record, "status": STATUS_SUSPENDED}
        new_alerts.append(alert_record)
        log({"event": "new_alert_recorded", "hash": unique_hash, "user": user_email, "suspended": suspended})

########################################################################################################################
#  MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN MAIN  #
########################################################################################################################

# Опис у документації.
if __name__ == "__main__":
    credentials = service_account.Credentials.from_service_account_file(SERVICE_ACCOUNT_FILE, scopes=SCOPES)
    simple_gmail_session = build(serviceName="gmail", version="v1", credentials=credentials.with_subject(HANDLER_USER))
    simple_admin_session = build(serviceName="admin", version="directory_v1",
                                 credentials=credentials.with_subject(ADMIN_USER))
    credentials = service_account.Credentials.from_service_account_file(SERVICE_ACCOUNT_FILE,
                                                                        scopes=SCOPES).with_subject(ADMIN_USER)
    stand_admin_session = google.auth.transport.requests.AuthorizedSession(credentials)
    del credentials

    USERS_LIST = []
    request = create_session(60, stand_admin_session, "get",
                             'https://admin.googleapis.com/admin/directory/v1/users?customer=my_customer',
                             query_type="&maxResults=100")
    for response in request:
        USERS_LIST.extend(response.get("users", []))
    del request, response

    role_assignments = []
    team_leader_members = []
    request = create_session(60, stand_admin_session, "get",
                             "https://admin.googleapis.com/admin/directory/v1/customer/my_customer/roleassignments",
                             query_type="?maxResults=100")
    for response in request:
        role_assignments.extend(response.get("items", []))
    for role in role_assignments:
        if role.get('roleId') == ORG_UNIT_TEAM_LEADER_ROLE_ID:
            team_leader_members.append(role['assignedTo'])
    del request, response, role_assignments, role

    alert_log = load_alert_log()
    alert_log = prune_alert_log(alert_log)

    process_action_responses(simple_gmail_session, simple_admin_session, alert_log)

    alert_log = prune_alert_log(load_alert_log())
    save_alert_log(alert_log)

    process_alert_requests(simple_gmail_session, simple_admin_session, USERS_LIST, team_leader_members, alert_log)

    save_alert_log(alert_log)