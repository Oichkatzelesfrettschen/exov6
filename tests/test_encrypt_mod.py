import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from encrypt_mod import XorEncryptModule
from stream_module import mblk_t


def test_xor_encrypt_decrypt_roundtrip():
    key = 0xAA
    mod = XorEncryptModule(key)
    msg = mblk_t(b"abc")
    encrypted = mod(msg)
    expected = bytes(b ^ key for b in b"abc")
    assert bytes(encrypted.data) == expected

    # Decrypt by applying the module again
    decrypted = mod(encrypted)
    assert bytes(decrypted.data) == b"abc"
