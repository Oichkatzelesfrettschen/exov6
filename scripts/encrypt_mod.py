from scripts.stream_module import mblk_t
from scripts.streams_log import strlog_json


class XorEncryptModule:
    """Simple XOR encryption/decryption module."""

    def __init__(self, key: int):
        self.key = key & 0xFF

    def __call__(self, mblk: mblk_t) -> mblk_t:
        """XOR each byte of the message and emit a log entry."""
        before = bytes(mblk.data)
        mblk.data = bytearray(b ^ self.key for b in mblk.data)
        strlog_json(
            "debug",
            "xor_encrypt",
            key=self.key,
            before=before.hex(),
            after=bytes(mblk.data).hex(),
        )
        return mblk
