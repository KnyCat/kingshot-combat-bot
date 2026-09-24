from __future__ import annotations

import hashlib
import hmac
import re
import secrets
import smtplib
import sqlite3
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from email.utils import formataddr
from typing import Any


EMAIL_PATTERN = re.compile(r"^[^\s@]+@[^\s@]+\.[^\s@]+$")
CODE_LIFETIME_MINUTES = 10
MAX_SENDS_PER_WINDOW = 3
SEND_WINDOW_MINUTES = 10
RESEND_COOLDOWN_SECONDS = 60
MAX_VERIFY_ATTEMPTS = 5


class EmailAuthError(Exception):
    pass


class EmailRateLimitError(EmailAuthError):
    pass


class EmailDeliveryError(EmailAuthError):
    pass


@dataclass(frozen=True)
class SmtpSettings:
    host: str
    port: int
    username: str
    password: str
    from_email: str
    use_ssl: bool = False
    use_starttls: bool = True

    @property
    def configured(self) -> bool:
        return bool(self.host and self.port and self.from_email)


def normalize_email(value: Any) -> str:
    email = str(value or "").strip().lower()
    if len(email) > 254 or not EMAIL_PATTERN.fullmatch(email):
        raise ValueError("Invalid email address")
    return email


def initialize_email_auth_schema(connection: sqlite3.Connection) -> None:
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS alliance_email_identities (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            user_id INTEGER NOT NULL UNIQUE,
            email_normalized TEXT NOT NULL UNIQUE,
            email_display TEXT NOT NULL,
            verified_at TEXT NOT NULL,
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL
        )
        """
    )
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS email_auth_challenges (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            email_normalized TEXT NOT NULL,
            purpose TEXT NOT NULL,
            target_user_id INTEGER,
            code_salt TEXT NOT NULL,
            code_digest TEXT NOT NULL,
            request_ip_digest TEXT NOT NULL,
            attempts INTEGER NOT NULL DEFAULT 0,
            max_attempts INTEGER NOT NULL DEFAULT 5,
            expires_at TEXT NOT NULL,
            used_at TEXT,
            created_at TEXT NOT NULL
        )
        """
    )
    connection.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_email_auth_challenge_lookup
        ON email_auth_challenges(email_normalized, purpose, created_at DESC)
        """
    )
    connection.execute(
        """
        CREATE INDEX IF NOT EXISTS idx_email_auth_challenge_ip
        ON email_auth_challenges(request_ip_digest, created_at DESC)
        """
    )


def _utc_now() -> datetime:
    return datetime.now(timezone.utc)


def _digest(secret_key: str, *parts: str) -> str:
    payload = "\x00".join(parts).encode("utf-8")
    return hmac.new(secret_key.encode("utf-8"), payload, hashlib.sha256).hexdigest()


def create_email_challenge(
    connection: sqlite3.Connection,
    *,
    email: str,
    purpose: str,
    target_user_id: int | None,
    request_ip: str,
    secret_key: str,
    now: datetime | None = None,
) -> str:
    normalized_email = normalize_email(email)
    normalized_purpose = str(purpose or "").strip().lower()
    if normalized_purpose not in {"login", "link"}:
        raise ValueError("Invalid email challenge purpose")
    if normalized_purpose == "link" and not target_user_id:
        raise ValueError("Link challenges require an authenticated user")

    current = now or _utc_now()
    current_iso = current.isoformat()
    window_start = (current - timedelta(minutes=SEND_WINDOW_MINUTES)).isoformat()
    cooldown_start = (current - timedelta(seconds=RESEND_COOLDOWN_SECONDS)).isoformat()
    ip_digest = _digest(secret_key, "ip", str(request_ip or "unknown"))

    recent_email = connection.execute(
        "SELECT COUNT(*) FROM email_auth_challenges WHERE email_normalized = ? AND created_at >= ?",
        (normalized_email, window_start),
    ).fetchone()[0]
    recent_ip = connection.execute(
        "SELECT COUNT(*) FROM email_auth_challenges WHERE request_ip_digest = ? AND created_at >= ?",
        (ip_digest, window_start),
    ).fetchone()[0]
    latest = connection.execute(
        "SELECT created_at FROM email_auth_challenges WHERE email_normalized = ? ORDER BY id DESC LIMIT 1",
        (normalized_email,),
    ).fetchone()
    if recent_email >= MAX_SENDS_PER_WINDOW or recent_ip >= MAX_SENDS_PER_WINDOW:
        raise EmailRateLimitError("Too many verification requests")
    if latest and str(latest[0]) >= cooldown_start:
        raise EmailRateLimitError("Please wait before requesting another code")

    code = f"{secrets.randbelow(1_000_000):06d}"
    salt = secrets.token_hex(16)
    digest = _digest(secret_key, "code", normalized_email, normalized_purpose, salt, code)
    expires_at = (current + timedelta(minutes=CODE_LIFETIME_MINUTES)).isoformat()

    connection.execute(
        """
        UPDATE email_auth_challenges
        SET used_at = ?
        WHERE email_normalized = ? AND purpose = ? AND used_at IS NULL
        """,
        (current_iso, normalized_email, normalized_purpose),
    )
    connection.execute(
        """
        INSERT INTO email_auth_challenges (
            email_normalized, purpose, target_user_id, code_salt, code_digest,
            request_ip_digest, attempts, max_attempts, expires_at, used_at, created_at
        ) VALUES (?, ?, ?, ?, ?, ?, 0, ?, ?, NULL, ?)
        """,
        (
            normalized_email,
            normalized_purpose,
            target_user_id,
            salt,
            digest,
            ip_digest,
            MAX_VERIFY_ATTEMPTS,
            expires_at,
            current_iso,
        ),
    )
    return code


def consume_email_challenge(
    connection: sqlite3.Connection,
    *,
    email: str,
    code: str,
    purpose: str,
    target_user_id: int | None,
    secret_key: str,
    now: datetime | None = None,
) -> bool:
    normalized_email = normalize_email(email)
    normalized_code = str(code or "").strip()
    if len(normalized_code) != 6 or not normalized_code.isdigit():
        return False

    current_iso = (now or _utc_now()).isoformat()
    row = connection.execute(
        """
        SELECT * FROM email_auth_challenges
        WHERE email_normalized = ? AND purpose = ? AND used_at IS NULL
          AND (target_user_id IS ? OR target_user_id = ?)
        ORDER BY id DESC LIMIT 1
        """,
        (normalized_email, purpose, target_user_id, target_user_id),
    ).fetchone()
    if not row or str(row["expires_at"]) <= current_iso or int(row["attempts"]) >= int(row["max_attempts"]):
        return False

    expected = _digest(
        secret_key,
        "code",
        normalized_email,
        purpose,
        str(row["code_salt"]),
        normalized_code,
    )
    if not hmac.compare_digest(expected, str(row["code_digest"])):
        connection.execute(
            "UPDATE email_auth_challenges SET attempts = attempts + 1 WHERE id = ?",
            (int(row["id"]),),
        )
        return False

    updated = connection.execute(
        "UPDATE email_auth_challenges SET used_at = ? WHERE id = ? AND used_at IS NULL",
        (current_iso, int(row["id"])),
    )
    return updated.rowcount == 1


def send_verification_email(settings: SmtpSettings, email: str, code: str) -> None:
    if not settings.configured:
        raise EmailDeliveryError("Email delivery is not configured")

    message = EmailMessage()
    message["Subject"] = f"{code} is your Kingshot verification code"
    message["From"] = formataddr(("Kingshot", settings.from_email))
    message["To"] = normalize_email(email)
    message.set_content(
        "Kingshot account verification\n\n"
        f"Your verification code is: {code}\n"
        f"It expires in {CODE_LIFETIME_MINUTES} minutes and can only be used once.\n\n"
        "Verificacion de cuenta Kingshot\n\n"
        f"Tu codigo de verificacion es: {code}\n"
        f"Caduca en {CODE_LIFETIME_MINUTES} minutos y solo se puede utilizar una vez.\n\n"
        "If you did not request this code, you can ignore this email.\n"
        "Si no has solicitado este codigo, puedes ignorar este correo."
    )
    message.add_alternative(
        f"""
                <!doctype html>
                <html lang="en">
                    <body style="margin:0;background:#0c1218;color:#eaf3ff;font-family:Arial,sans-serif;">
                        <div style="display:none;max-height:0;overflow:hidden;">Your Kingshot verification code is {code}</div>
                        <table role="presentation" width="100%" cellspacing="0" cellpadding="0" style="background:#0c1218;padding:32px 14px;">
                            <tr><td align="center">
                                <table role="presentation" width="100%" cellspacing="0" cellpadding="0" style="max-width:520px;background:#111c26;border:1px solid #294156;border-radius:8px;">
                                    <tr>
                                        <td style="padding:24px 28px 16px;text-align:center;">
                                            <img src="https://kingshot.es/static/favicon.webp" width="64" height="64" alt="Kingshot" style="display:block;margin:0 auto 14px;border-radius:8px;">
                                            <div style="font-size:24px;font-weight:800;color:#ffffff;">Kingshot</div>
                                        </td>
                                    </tr>
                                    <tr>
                                        <td style="padding:8px 28px 28px;text-align:center;">
                                            <h1 style="margin:0 0 10px;font-size:22px;color:#ffffff;">Verify your account</h1>
                                            <p style="margin:0 0 20px;color:#b9cad9;line-height:1.5;">Use this code to complete your sign-in:</p>
                                            <div style="display:inline-block;padding:16px 24px;border:1px solid #e5b94f;border-radius:8px;background:#0b141c;color:#f2c76a;font-size:32px;font-weight:800;letter-spacing:8px;">{code}</div>
                                            <p style="margin:20px 0 4px;color:#dce8f2;line-height:1.5;">This code expires in {CODE_LIFETIME_MINUTES} minutes and can only be used once.</p>
                                            <p style="margin:0;color:#91a8bb;line-height:1.5;">Este codigo caduca en {CODE_LIFETIME_MINUTES} minutos y solo se puede utilizar una vez.</p>
                                        </td>
                                    </tr>
                                    <tr>
                                        <td style="padding:18px 28px;border-top:1px solid #294156;color:#7890a4;font-size:12px;line-height:1.5;text-align:center;">
                                            If you did not request this code, you can safely ignore this email.<br>
                                            Si no has solicitado este codigo, puedes ignorar este correo.
                                        </td>
                                    </tr>
                                </table>
                            </td></tr>
                        </table>
                    </body>
                </html>
            """,
            subtype="html",
            )

    try:
        smtp_type = smtplib.SMTP_SSL if settings.use_ssl else smtplib.SMTP
        with smtp_type(settings.host, settings.port, timeout=10) as client:
            if settings.use_starttls and not settings.use_ssl:
                client.starttls()
            if settings.username:
                client.login(settings.username, settings.password)
            client.send_message(message)
    except (OSError, smtplib.SMTPException) as exc:
        raise EmailDeliveryError("Could not send verification email") from exc