#!/usr/bin/env python3
import os
import subprocess
import sys
from pathlib import Path

# Paths
ROOT = Path(__file__).resolve().parents[2]
LIBOS = ROOT / "libos"
INCLUDE = ROOT / "include"
TEST_DIR = ROOT / "tests/posix"
SMOKE_TEST = TEST_DIR / "smoke_test.c"

def compile_and_run(name, sources, defs=[]):
    print(f"--- Running Test: {name} ---")
    exe = TEST_DIR / f"test_{name}"

    cmd = [
        "gcc",
        "-std=gnu11", # Need gnu11 for some posix stuff
        "-Wall",
        "-Werror",
        "-I", str(ROOT),
        "-I", str(INCLUDE),
        "-I", str(LIBOS),
        "-I", str(ROOT / "include/libos"), # If exists
        "-lpthread", # process.c uses thread locals?
    ]

    for d in defs:
        cmd.append(f"-D{d}")

    cmd += [str(s) for s in sources]
    cmd += ["-o", str(exe)]

    print(f"Compiling: {' '.join(cmd)}")
    try:
        subprocess.check_call(cmd)
    except subprocess.CalledProcessError:
        print("Compilation FAILED")
        return False

    print(f"Running: {exe}")
    try:
        subprocess.check_call([str(exe)])
        print("PASSED")
        return True
    except subprocess.CalledProcessError:
        print("Execution FAILED")
        return False
    finally:
        if exe.exists():
            exe.unlink()

def main():
    results = []

    # Configuration 1: Host Wrappers (posix.c only)
    sources1 = [
        SMOKE_TEST,
        LIBOS / "posix/posix.c",
        LIBOS / "libfs_stubs.c",
    ]
    results.append(compile_and_run("host_wrappers", sources1))

    # Configuration 2: Native Process (posix.c + process.c)
    # process.c overrides weak symbols in posix.c
    sources2 = [
        SMOKE_TEST,
        LIBOS / "posix/posix.c",
        LIBOS / "process.c",
        LIBOS / "libfs_stubs.c",
    ]
    results.append(compile_and_run("native_process", sources2))

    if all(results):
        print("\nAll tests PASSED.")
        sys.exit(0)
    else:
        print("\nSome tests FAILED.")
        sys.exit(1)

if __name__ == "__main__":
    main()
