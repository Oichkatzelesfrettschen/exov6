#!/usr/bin/env python3
"""Unified build helper for the FeuerBird project."""

from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys
from typing import List


def run_cmake(build_dir: pathlib.Path, build_type: str) -> None:
    """Configure and build the project using CMake."""
    type_map = {
        "debug": "Debug",
        "release": "Release",
        "performance": "Release",
    }
    cmake_args: List[str] = [
        "cmake",
        "-S",
        ".",
        "-B",
        str(build_dir),
        "-G",
        "Ninja",
        "-DCMAKE_C_COMPILER=clang",
        "-DCMAKE_CXX_COMPILER=clang++",
        f"-DCMAKE_BUILD_TYPE={type_map.get(build_type, 'Debug')}",
        "-DCMAKE_C_STANDARD=23",
        "-DCMAKE_CXX_STANDARD=23",
        "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
        "-DCMAKE_C_FLAGS=-Wall -Werror -std=c23",
        "-DCMAKE_CXX_FLAGS=-Wall -Werror -std=c++23",
    ]
    if build_type == "performance":
        cmake_args.append("-DCMAKE_C_FLAGS_RELEASE=-O3")
    subprocess.check_call(cmake_args)
    subprocess.check_call(["ninja", "-C", str(build_dir)])
    cc_json = build_dir / "compile_commands.json"
    if cc_json.exists():
        cc_json.replace("compile_commands.json")


def run_meson(build_dir: pathlib.Path, build_type: str) -> None:
    """Configure and build the project using Meson."""
    meson_type = "debug" if build_type == "debug" else "release"
    meson_args: List[str] = [
        "meson",
        "setup",
        "--reconfigure",
        f"--buildtype={meson_type}",
        str(build_dir),
        ".",
    ]
    if build_type == "performance":
        meson_args += ["-Db_lto=true", "-Db_pie=true"]
    subprocess.check_call(meson_args)
    subprocess.check_call(["ninja", "-C", str(build_dir)])
    cc_json = build_dir / "compile_commands.json"
    if cc_json.exists():
        cc_json.replace("compile_commands.json")


def main() -> int:
    """Entry point for the build helper."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "-s",
        "--system",
        choices=["cmake", "meson"],
        default="cmake",
        help="Build system to use",
    )
    parser.add_argument(
        "-t",
        "--type",
        choices=["debug", "release", "performance"],
        default="debug",
        help="Build type to configure",
    )
    parser.add_argument(
        "-o",
        "--outdir",
        default="build",
        help="Directory for build artifacts",
    )
    args = parser.parse_args()

    build_dir = pathlib.Path(args.outdir)
    build_dir.mkdir(parents=True, exist_ok=True)

    try:
        if args.system == "cmake":
            run_cmake(build_dir, args.type)
        else:
            run_meson(build_dir, args.type)
    except subprocess.CalledProcessError as exc:
        return exc.returncode
    return 0


if __name__ == "__main__":
    sys.exit(main())
