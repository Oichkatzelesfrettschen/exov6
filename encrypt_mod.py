from stream_module import mblk_t

class XorEncryptModule:
    """Simple XOR encryption/decryption module."""

    def __init__(self, key: int):
        self.key = key & 0xFF

    def __call__(self, mblk: mblk_t) -> mblk_t:
        mblk.data = bytearray(b ^ self.key for b in mblk.data)
        return mblk
