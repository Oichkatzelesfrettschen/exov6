import os
import shutil
import subprocess
import random
import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))

# simple python model mirroring formal specs

def compute_tag(i, r, o):
    return i + r + o

def cap_new(i, r, o):
    return {"id": i, "rights": r, "owner": o, "tag": compute_tag(i, r, o)}

def cap_verify(c):
    return compute_tag(c["id"], c["rights"], c["owner"]) == c["tag"]

def cap_has_rights(r, need):
    return (r & need) == need


def test_cap_new_verify():
    for _ in range(100):
        i = random.randint(0, 1000)
        rights = random.randint(0, 15)
        owner = random.randint(0, 1000)
        c = cap_new(i, rights, owner)
        assert cap_verify(c)


def test_cap_has_rights_prop():
    for _ in range(100):
        rights = random.randint(0, 15)
        need = random.randint(0, 15)
        assert cap_has_rights(rights, need) == ((rights & need) == need)


def test_coq_build():
    if not shutil.which("coqc"):
        pytest.skip("coqc not installed")
    subprocess.check_call(["make", "-C", os.path.join(ROOT, "formal", "coq")])


def test_tla_model():
    if not shutil.which("tlc"):
        pytest.skip("tlc not installed")
    subprocess.check_call(["tlc", os.path.join(ROOT, "formal", "specs", "tla", "ExoCap.tla")])
