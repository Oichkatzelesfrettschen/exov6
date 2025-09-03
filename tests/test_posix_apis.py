import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

SRC_FILES = [
    ROOT / "user/posix_file_test.c",
    ROOT / "user/posix_signal_test.c",
    ROOT / "user/posix_pipe_test.c",
    ROOT / "user/posix_rename_unlink_test.c",
    ROOT / "user/posix_ftruncate_test.c",
    ROOT / "demos/posix_misc_test.c",
    ROOT / "demos/posix_socket_test.c",
    ROOT / "demos/posix_cwd_test.c",
]


def compile_and_run(source: pathlib.Path) -> None:
    with tempfile.TemporaryDirectory() as td:
        exe = pathlib.Path(td) / "test"
        inc_dir = pathlib.Path(td) / "include"
        inc_dir.mkdir()
        host_header = ROOT / "include/exokernel.h"
        (inc_dir / "exokernel.h").write_text(
            f'#include <stddef.h>\n#include "{host_header}"\n'
        )
        cmd = [
            "gcc",
            "-std=c17",
            "-Wall",
            "-Werror",
            "-I",
            str(td),
            "-I",
            str(ROOT),
            "-I",
            str(ROOT / "libos"),
            "-I",
            str(ROOT / "include/libos"),
            "-idirafter",
            str(ROOT / "include"),
            str(source),
            str(ROOT / "libos/posix.c"),
            str(ROOT / "libos/fs.c"),
            str(ROOT / "libos/file.c"),
            str(ROOT / "libos/fs_ufs.c"),
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


def test_posix_ftruncate_ops():
    compile_and_run(SRC_FILES[4])


def test_posix_socket_ops():
    compile_and_run(SRC_FILES[5])
