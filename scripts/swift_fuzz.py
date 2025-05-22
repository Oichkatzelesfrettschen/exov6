#!/usr/bin/env python3
"""Build and run the Swift libFuzzer target."""

import argparse
import subprocess
from pathlib import Path


def build_fuzzer(root: Path) -> Path:
    src = root / "fuzz.swift"
    out = root / "fuzz"
    cmd = [
        "swiftc",
        "-sanitize=fuzzer,address",
        "-parse-as-library",
        str(src),
        "-o",
        str(out),
    ]
    subprocess.run(cmd, check=True)
    return out


def run_fuzzer(executable: Path, args):
    subprocess.run([str(executable), *args], check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Swift libFuzzer helper")
    parser.add_argument(
        "fuzzer_args", nargs=argparse.REMAINDER, help="Arguments for the fuzzer"
    )
    opts = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    exe = build_fuzzer(root)
    run_fuzzer(exe, opts.fuzzer_args)


if __name__ == "__main__":
    main()
