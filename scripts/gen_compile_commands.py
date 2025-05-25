#!/usr/bin/env python3
"""Generate compile_commands.json via CMake or Meson."""

import argparse
import os
import shutil
import subprocess
import sys


def run_cmake(cmake_args: list[str]) -> None:
    build_dir = "build"
    os.makedirs(build_dir, exist_ok=True)
    cmd = [
        "cmake",
        "-S",
        ".",
        "-B",
        build_dir,
        "-G",
        "Ninja",
        "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
    ] + cmake_args
    subprocess.check_call(cmd)
    src = os.path.join(build_dir, "compile_commands.json")
    if os.path.exists(src):
        shutil.copy(src, "compile_commands.json")
    else:
        raise FileNotFoundError(src)


def run_meson(path: str) -> None:
    build_dir = "build"
    cmd = [
        "meson",
        "setup",
        "--wipe",
        "--buildtype=release",
        build_dir,
        path,
    ]
    subprocess.check_call(cmd)
    src = os.path.join(build_dir, "compile_commands.json")
    if os.path.exists(src):
        shutil.copy(src, "compile_commands.json")
    else:
        raise FileNotFoundError(src)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--meson", metavar="PATH", help="Meson project path")
    parser.add_argument(
        "cmake_args", nargs=argparse.REMAINDER, help="Extra CMake arguments"
    )
    args = parser.parse_args()

    try:
        if args.meson:
            run_meson(args.meson)
        else:
            run_cmake(args.cmake_args)
    except subprocess.CalledProcessError as exc:
        return exc.returncode
    except Exception as exc:  # pylint: disable=broad-except
        sys.stderr.write(f"{exc}\n")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
