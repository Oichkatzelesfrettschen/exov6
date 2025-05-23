import pathlib
import sys

# Ensure repository root is in sys.path
ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import simulate

def test_simulate_harness_completes():
    assert simulate.main() == 0
