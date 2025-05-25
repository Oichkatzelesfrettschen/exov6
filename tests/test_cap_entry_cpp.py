import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

CPP_CODE = textwrap.dedent("""
#include <iostream>
#include "src-headers/cap.h"
int main(){
    std::cout << sizeof(struct cap_entry) << ' ' << alignof(struct cap_entry);
    return 0;
}
""")

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.cpp"
        exe = pathlib.Path(td)/"test"
        src.write_text(CPP_CODE)
        subprocess.check_call([
            "g++","-std=c++17","-Wall","-Werror",
            "-iquote", str(ROOT),
            "-iquote", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        out = subprocess.check_output([str(exe)], text=True)
        return out.strip()

def test_cap_entry_cpp_size():
    assert compile_and_run() == "20 4"
