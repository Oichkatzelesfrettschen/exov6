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
    lines = [l for l in capsys.readouterr().out.strip().splitlines() if l]
    assert len(lines) == 2
    for idx, line in enumerate(lines, 1):
        assert re.match(rf"^{idx} modules: [0-9.]+ us$", line)
