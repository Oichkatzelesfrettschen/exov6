import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from examples.python.stream_module import mblk_t, attach_module


def test_attach_module_pipeline_order():
    def to_upper(mblk: mblk_t) -> mblk_t:
        mblk.data = bytearray(mblk.data.upper())
        return mblk

    def add_exclam(mblk: mblk_t) -> mblk_t:
        mblk.data += b"!"
        return mblk

    pipeline = attach_module([to_upper, add_exclam])

    msg = mblk_t(b"hello")
    result = pipeline(msg)
    assert bytes(result.data) == b"HELLO!"
