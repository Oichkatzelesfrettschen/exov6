#!/usr/bin/env python3
"""Latency test harness for STREAMS module stack."""

import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from encrypt_mod import XorEncryptModule
from stream_module import mblk_t, attach_module


def main() -> None:
    key = 0x55
    pipeline = attach_module([XorEncryptModule(key)])
    iterations = 10000
    start = time.perf_counter()
    for _ in range(iterations):
        msg = mblk_t(b"hello")
        pipeline(msg)
    elapsed = time.perf_counter() - start
    print(f"Average latency: {elapsed / iterations * 1e6:.2f} us")


if __name__ == "__main__":
    main()
