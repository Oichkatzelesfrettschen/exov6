import pathlib
import sys
import json
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from examples.python.streams_log import strlog_json


def test_strlog_json_timestamp_format(capsys):
    strlog_json("info", "hello", foo="bar")
    captured = capsys.readouterr().err.strip()
    record = json.loads(captured)
    assert record["level"] == "info"
    assert record["msg"] == "hello"
    assert record["foo"] == "bar"
    assert re.match(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$", record["ts"])


def test_strlog_json_outputs_to_stderr(capsys):
    strlog_json("error", "boom", code=123)
    captured = capsys.readouterr()
    assert captured.out == ""
    record = json.loads(captured.err)
    assert record["level"] == "error"
    assert record["msg"] == "boom"
    assert record["code"] == 123


def test_strlog_json_includes_all_fields(capsys):
    strlog_json("debug", "hi", a=1, b="two")
    record = json.loads(capsys.readouterr().err)
    assert record["a"] == 1
    assert record["b"] == "two"
