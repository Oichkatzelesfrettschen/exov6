#!/usr/bin/env python3
"""Latency test harness for STREAMS module stack."""

import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from encrypt_mod import XorEncryptModule
from stream_module import mblk_t, attach_module


def _run_pipeline(modules: list) -> float:
    pipeline = attach_module(modules)
    iterations = 10000
    start = time.perf_counter()
    for _ in range(iterations):
        msg = mblk_t(b"hello")
        pipeline(msg)
    elapsed = time.perf_counter() - start
    return elapsed / iterations


def main() -> None:
    combos = [
        [XorEncryptModule(0x55)],
        [XorEncryptModule(0x55), XorEncryptModule(0xAA)],
    ]

    for mods in combos:
        avg = _run_pipeline(mods)
        print(f"{len(mods)} modules: {avg * 1e6:.2f} us")


if __name__ == "__main__":
    main()
