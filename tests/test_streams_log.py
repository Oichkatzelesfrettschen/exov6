import pathlib
import sys
import json
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from streams_log import strlog_json


def test_strlog_json_timestamp_format(capsys):
    strlog_json("info", "hello", foo="bar")
    captured = capsys.readouterr().err.strip()
    record = json.loads(captured)
    assert record["level"] == "info"
    assert record["msg"] == "hello"
    assert record["foo"] == "bar"
    assert re.match(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$", record["ts"])
