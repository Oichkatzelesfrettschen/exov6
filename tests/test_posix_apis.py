import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

SRC_FILES = [
    ROOT / 'src-uland/posix_file_test.c',
    ROOT / 'src-uland/posix_signal_test.c',
    ROOT / 'src-uland/posix_pipe_test.c',
    ROOT / 'tests/posix/dlopen_test.c',
]


def compile_and_run(source: pathlib.Path) -> None:
    with tempfile.TemporaryDirectory() as td:
        exe = pathlib.Path(td) / 'test'
        subprocess.check_call([
            'gcc', '-std=c2x', '-Wall', '-Werror',
            '-idirafter', str(ROOT / 'src-headers'),
            str(source),
            '-o', str(exe),
        ])
        subprocess.check_call([str(exe)])


def test_posix_file_ops():
    compile_and_run(SRC_FILES[0])


def test_posix_signal_ops():
    compile_and_run(SRC_FILES[1])


def test_posix_pipe_ops():
    compile_and_run(SRC_FILES[2])


def test_dlopen():
    compile_and_run(SRC_FILES[3])
