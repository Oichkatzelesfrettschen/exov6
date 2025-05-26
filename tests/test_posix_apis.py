import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

SRC_FILES = [
    ROOT / "engine/user/posix_file_test.c",
    ROOT / "engine/user/posix_signal_test.c",
    ROOT / "engine/user/posix_pipe_test.c",
    ROOT / "engine/user/user/posix_misc_test.c",
    ROOT / "engine/user/user/posix_socket_test.c",
    ROOT / "engine/user/user/posix_cwd_test.c",
]


def compile_and_run(source: pathlib.Path) -> None:
    with tempfile.TemporaryDirectory() as td:
        exe = pathlib.Path(td) / "test"
        inc_dir = pathlib.Path(td) / "include"
        inc_dir.mkdir()
        (inc_dir / "exokernel.h").write_text(
            '#include <stddef.h>\n#include "../engine/include/exokernel.h"\n'
        )
        cmd = [
            "gcc",
            "-std=c2x",
            "-Wall",
            "-Werror",
            "-I",
            str(td),
            "-I",
            str(ROOT),
            "-I",
            str(ROOT / "engine/libos/include"),
            "-I",
            str(ROOT / "engine/libos"),
            "-I",
            str(ROOT / "engine/include/libos"),
            "-idirafter",
            str(ROOT / "engine/include"),
            str(source),
            str(ROOT / "engine/libos/posix.c"),
            str(ROOT / "engine/libos/fs.c"),
            str(ROOT / "engine/libos/file.c"),
            str(ROOT / "engine/libos/fs_ufs.c"),
            str(ROOT / "tests/libos_host_stubs.c"),
            "-o",
            str(exe),
        ]
        subprocess.check_call(cmd)
        subprocess.check_call([str(exe)])


def test_posix_file_ops():
    compile_and_run(SRC_FILES[0])


def test_posix_signal_ops():
    compile_and_run(SRC_FILES[1])


def test_posix_pipe_ops():
    compile_and_run(SRC_FILES[2])


def test_posix_misc_ops():
    compile_and_run(SRC_FILES[3])


def test_posix_socket_ops():
    compile_and_run(SRC_FILES[4])
