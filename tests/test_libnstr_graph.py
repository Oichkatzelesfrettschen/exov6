import pathlib
import subprocess
import ctypes

ROOT = pathlib.Path(__file__).resolve().parents[1]

LIB = ROOT / 'libnstr_graph.so'

def build_lib():
    if not LIB.exists():
        subprocess.check_call(['make', 'libnstr_graph.so'], cwd=ROOT)


def load_lib():
    build_lib()
    return ctypes.CDLL(str(LIB))


def test_basic_graph_ops():
    lib = load_lib()
    lib.nstr_graph_open.restype = ctypes.c_void_p
    lib.nstr_graph_close.argtypes = [ctypes.c_void_p]
    lib.nstr_graph_add_edge.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
    lib.nstr_graph_remove_edge.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
    lib.nstr_graph_query.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
    lib.nstr_graph_query.restype = ctypes.c_int

    g = lib.nstr_graph_open()
    assert g

    assert lib.nstr_graph_query(g, 1, 2) == 0
    assert lib.nstr_graph_add_edge(g, 1, 2) == 0
    assert lib.nstr_graph_query(g, 1, 2) == 1
    assert lib.nstr_graph_remove_edge(g, 1, 2) == 0
    assert lib.nstr_graph_query(g, 1, 2) == 0

    lib.nstr_graph_close(g)
