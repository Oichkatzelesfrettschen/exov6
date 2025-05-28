#!/usr/bin/env python3
"""Latency test harness for STREAMS module stack.

This script chains together various STREAMS modules and measures the
latency of processing a simple ``mblk_t`` message through the pipeline.
Multiple module combinations are tested so that changes to individual
modules can be evaluated in isolation.
"""

import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

import statistics

from scripts.encrypt_mod import XorEncryptModule
from scripts.stream_module import mblk_t, attach_module


class UpperCaseModule:
    """Transform message bytes to upper case."""

    def __call__(self, mblk: mblk_t) -> mblk_t:
        mblk.data = bytearray(mblk.data.upper())
        return mblk


class ReverseModule:
    """Reverse the byte order of the message."""

    def __call__(self, mblk: mblk_t) -> mblk_t:
        mblk.data.reverse()
        return mblk


def _measure_latency(pipeline, iterations: int) -> dict[str, float]:
    """Return average, minimum and maximum latency in microseconds."""

    samples = []
    for _ in range(iterations):
        msg = mblk_t(b"hello")
        start = time.perf_counter_ns()
        pipeline(msg)
        samples.append(time.perf_counter_ns() - start)

    return {
        "avg": statistics.mean(samples) / 1000.0,
        "min": min(samples) / 1000.0,
        "max": max(samples) / 1000.0,
    }


def main() -> None:
    """Run latency measurements for several module configurations."""

    key = 0x55
    configs = [
        ("xor", [XorEncryptModule(key)]),
        ("upper+xor", [UpperCaseModule(), XorEncryptModule(key)]),
        (
            "reverse+upper+xor",
            [ReverseModule(), UpperCaseModule(), XorEncryptModule(key)],
        ),
    ]

    iterations = 10000
    for name, modules in configs:
        pipeline = attach_module(modules)
        metrics = _measure_latency(pipeline, iterations)
        print(
            f"{name}: avg {metrics['avg']:.2f} us "
            f"(min {metrics['min']:.2f}, max {metrics['max']:.2f})"
        )


if __name__ == "__main__":
    main()
