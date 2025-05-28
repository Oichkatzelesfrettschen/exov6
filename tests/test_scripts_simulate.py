import pathlib
import sys
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts import streams_latency as script


def test_pipeline_transformation_roundtrip():
    pipeline = script.attach_module([script.XorEncryptModule(0x55)])
    msg = script.mblk_t(b"hello")
    pipeline(msg)
    # Decrypt to verify roundtrip
    pipeline(msg)
    assert bytes(msg.data) == b"hello"


def test_latency_reported(capsys):
    script.main()
    lines = capsys.readouterr().out.strip().splitlines()
    assert len(lines) == 3
    pattern = re.compile(r"^[a-z+]+: avg [0-9.]+ us \(min [0-9.]+, max [0-9.]+\)$")
    for line in lines:
        assert pattern.match(line)
