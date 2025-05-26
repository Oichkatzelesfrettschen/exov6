#!/usr/bin/env python3
"""Monte Carlo simulation of lock acquisition ordering.

Two threads (STREAMS and RPC) each need to acquire the locks
``STREAMS_LOCK`` and ``RPC_LOCK``. The order in which each thread
acquires the locks is chosen randomly. Their executions are randomly
interleaved, modelling a simple scheduler.

The simulation counts how often a circular wait occurs, leading to a
deadlock. A few sample sequences that trigger deadlock are printed
along with the overall probability.
"""

from __future__ import annotations

import argparse
import random
from typing import List, Tuple

LOCKS = ("STREAMS_LOCK", "RPC_LOCK")


class ThreadSim:
    def __init__(self, name: str) -> None:
        self.name = name
        self.order = random.sample(LOCKS, k=len(LOCKS))
        self.index = 0
        self.holding: List[str] = []
        self.done = False

    def next_lock(self) -> str:
        return self.order[self.index]


def run_trial() -> Tuple[bool, List[str]]:
    """Run a single randomized execution.

    Returns ``(deadlock, log)`` where ``deadlock`` indicates if a
    circular wait occurred.
    """
    locks = {l: None for l in LOCKS}
    threads = [ThreadSim("STREAMS"), ThreadSim("RPC")]
    log: List[str] = []

    while True:
        random.shuffle(threads)
        progress = False
        for t in threads:
            if t.done:
                continue
            lock = t.next_lock()
            if locks[lock] is None:
                locks[lock] = t.name
                t.holding.append(lock)
                log.append(f"{t.name} acquire {lock}")
                t.index += 1
                progress = True
                if t.index == len(t.order):
                    for l in reversed(t.holding):
                        locks[l] = None
                        log.append(f"{t.name} release {l}")
                    t.done = True
            else:
                log.append(f"{t.name} wait {lock}")

        if not progress:
            log.append("DEADLOCK")
            return True, log
        if all(t.done for t in threads):
            return False, log


def main(trials: int, sample: int) -> None:
    deadlock_logs: List[List[str]] = []
    deadlocks = 0
    for _ in range(trials):
        is_deadlock, log = run_trial()
        if is_deadlock:
            deadlocks += 1
            if len(deadlock_logs) < sample:
                deadlock_logs.append(log)

    probability = deadlocks / trials if trials else 0.0
    print(f"Deadlock probability: {probability:.4f} ({deadlocks}/{trials})")
    if deadlock_logs:
        print("\nSample deadlock sequences:")
        for seq in deadlock_logs:
            print("- " + " | ".join(seq))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Simulate STREAMS/RPC lock ordering")
    parser.add_argument("-n", "--trials", type=int, default=10000,
                        help="number of simulation runs")
    parser.add_argument("-s", "--samples", type=int, default=5,
                        help="number of deadlock logs to display")
    args = parser.parse_args()
    main(args.trials, args.samples)

