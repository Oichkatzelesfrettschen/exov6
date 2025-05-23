import pathlib
import sys
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts import simulate as script


def test_pipeline_transformation_roundtrip():
    pipeline = script.attach_module([script.XorEncryptModule(0x55)])
    msg = script.mblk_t(b"hello")
    pipeline(msg)
    # Decrypt to verify roundtrip
    pipeline(msg)
    assert bytes(msg.data) == b"hello"


def test_latency_reported(capsys):
    script.main()
    captured = capsys.readouterr().out.strip()
    assert re.match(r"^Average latency: [0-9.]+ us$", captured)
