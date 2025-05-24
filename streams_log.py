import json
import sys
from datetime import datetime, UTC


def strlog(message: str) -> None:
    """Output a plain text log message."""
    print(message)


def strlog_json(level: str, message: str, **fields) -> None:
    """Emit a structured log entry as JSON.

    Parameters
    ----------
    level:
        Severity of the message (e.g. "info", "error").
    message:
        Human readable log message.
    **fields:
        Additional keyword arguments are included in the output record.
    """
    record = {
        "ts": datetime.now(UTC).isoformat(timespec="seconds"),
        "level": level,
        "msg": message,
    }
    record.update(fields)
    print(json.dumps(record), file=sys.stderr)
