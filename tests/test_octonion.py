import os
import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]
CC = os.environ.get("CC", "clang")

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <math.h>
#include "include/octonion.h"

static int nearly_equal(double a, double b) {
  return fabs(a - b) < 1e-9;
}

int main(void) {
  octonion_t a = {{1, 2, 3, 4, 5, 6, 7, 8}};
  octonion_t b = {{2, -1, 0.5, -3, 1, -1, 0.1, 2.5}};
  octonion_t c = {{0.3, 0.2, 0.1, -0.4, 1, 0, -0.2, 0.5}};

  octonion_t ab = octonion_multiply(a, b);
  octonion_t bc = octonion_multiply(b, c);
  octonion_t ab_c = octonion_multiply(ab, c);
  octonion_t a_bc = octonion_multiply(a, bc);
  assert(!octonion_equals(&ab_c, &a_bc));

  double norm_ab = octonion_norm(ab);
  double expected = octonion_norm(a) * octonion_norm(b);
  assert(nearly_equal(norm_ab, expected));

  octonion_t inv_a = octonion_inverse(a);
  octonion_t one = octonion_multiply(a, inv_a);
  assert(nearly_equal(one.e0, 1.0));
  assert(nearly_equal(one.e1, 0.0));
  assert(nearly_equal(one.e2, 0.0));
  assert(nearly_equal(one.e3, 0.0));
  assert(nearly_equal(one.e4, 0.0));
  assert(nearly_equal(one.e5, 0.0));
  assert(nearly_equal(one.e6, 0.0));
  assert(nearly_equal(one.e7, 0.0));

  return 0;
}
"""
)


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        src.write_text(C_CODE)
        exe = pathlib.Path(td) / "test"
        subprocess.check_call(
            [
                CC,
                "-std=c2x",
                "-O3",
                "-march=native",
                "-ffast-math",
                "-fstrict-aliasing",
                "-fomit-frame-pointer",
                "-funroll-loops",
                "-pipe",
                "-Wall",
                "-Werror",
                "-I",
                str(ROOT),
                "-idirafter",
                str(ROOT / "include"),
                str(src),
                "-lm",
                "-o",
                str(exe),
            ]
        )
        return subprocess.run([str(exe)]).returncode


def test_octonion_algebra():
    assert compile_and_run() == 0
