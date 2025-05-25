import pathlib
import sys
import json
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from streams_log import strlog, strlog_json


def test_strlog_json_timestamp_format(capsys):
    strlog_json("info", "hello", foo="bar")
    captured = capsys.readouterr().err.strip()
    record = json.loads(captured)
    assert record["level"] == "info"
    assert record["msg"] == "hello"
    assert record["foo"] == "bar"
    assert re.match(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$", record["ts"])


def test_strlog_plain_text(capsys):
    strlog("plain message")
    captured = capsys.readouterr().out.strip()
    assert captured == "plain message"


def test_strlog_json_extra_fields(capsys):
    strlog_json("debug", "hi", alpha=1, beta="b")
    record = json.loads(capsys.readouterr().err.strip())
    assert record["alpha"] == 1
    assert record["beta"] == "b"
