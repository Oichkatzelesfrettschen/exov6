#!/usr/bin/env python3
"""
Lock Inventory Automation Script
Phase 7.1: Automated Lock Migration Analysis

Scans ExoV6 kernel codebase to identify all lock declarations and usage,
categorizes them by type, and generates migration recommendations.

Usage: ./lock_inventory.py [kernel_dir]
Output: LOCK_MIGRATION_INVENTORY.txt
"""

import re
import os
import sys
from pathlib import Path
from collections import defaultdict
from typing import List, Dict, Tuple

# Lock type patterns
LOCK_PATTERNS = {
    'spinlock': r'struct\s+spinlock\s+(\w+)',
    'sleeplock': r'struct\s+sleeplock\s+(\w+)',
    'qspinlock': r'struct\s+qspinlock\s+(\w+)',
    'adaptive_mutex': r'struct\s+adaptive_mutex\s+(\w+)',
    'lwkt_token': r'struct\s+lwkt_token\s+(\w+)',
}

# Lock initialization patterns
INIT_PATTERNS = {
    'initlock': r'initlock\s*\(\s*&([^,]+)',
    'initsleeplock': r'initsleeplock\s*\(\s*&([^,]+)',
    'qspin_init': r'qspin_init\s*\(\s*&([^,]+)',
    'adaptive_mutex_init': r'adaptive_mutex_init\s*\(\s*&([^,]+)',
    'lwkt_token_init': r'lwkt_token_init\s*\(\s*&([^,]+)',
}

# Lock acquisition patterns
ACQUIRE_PATTERNS = {
    'acquire': r'acquire\s*\(\s*&([^)]+)',
    'release': r'release\s*\(\s*&([^)]+)',
    'acquiresleep': r'acquiresleep\s*\(\s*&([^)]+)',
    'releasesleep': r'releasesleep\s*\(\s*&([^)]+)',
    'qspin_lock': r'qspin_lock\s*\(\s*&([^)]+)',
    'qspin_unlock': r'qspin_unlock\s*\(\s*&([^)]+)',
}

# Subsystem classification based on file path
SUBSYSTEM_MAP = {
    'sched': ['proc', 'sched', 'fork'],
    'memory': ['kalloc', 'vm', 'mmu'],
    'filesystem': ['fs', 'bio', 'log', 'inode', 'file'],
    'device': ['console', 'ide', 'uart', 'kbd'],
    'ipc': ['pipe', 'ipc', 'exo_disk'],
    'sync': ['spinlock', 'sleeplock', 'qspinlock', 'mutex'],
}

# Priority levels for migration
PRIORITY_MAP = {
    'sched': 'P0-Critical',      # Already done in Phase 5.3
    'memory': 'P0-Critical',     # Already done in Phase 5.4
    'device': 'P1-High',         # Phase 7.3
    'filesystem': 'P1-High',     # Phase 7.2
    'ipc': 'P2-Medium',
    'sync': 'P3-Infrastructure',
}

class LockInfo:
    """Information about a single lock in the codebase"""
    def __init__(self, name: str, lock_type: str, file_path: str, line_num: int):
        self.name = name
        self.lock_type = lock_type
        self.file_path = file_path
        self.line_num = line_num
        self.subsystem = self._classify_subsystem()
        self.priority = PRIORITY_MAP.get(self.subsystem, 'P3-Low')
        self.init_sites = []
        self.acquire_sites = []
        self.recommended_type = self._recommend_type()

    def _classify_subsystem(self) -> str:
        """Classify lock by subsystem based on file path"""
        path_lower = self.file_path.lower()
        for subsys, keywords in SUBSYSTEM_MAP.items():
            if any(kw in path_lower for kw in keywords):
                return subsys
        return 'other'

    def _recommend_type(self) -> str:
        """Recommend modern lock type based on usage patterns"""
        if self.lock_type == 'qspinlock':
            return 'qspinlock (already modern)'
        elif self.lock_type == 'adaptive_mutex':
            return 'adaptive_mutex (already modern)'
        elif self.lock_type == 'lwkt_token':
            return 'lwkt_token (already modern)'
        elif self.lock_type == 'sleeplock':
            # Sleeplocks are for long-duration I/O - keep as sleeplock but modernize
            return 'sleeplock (modernized in Phase 6)'
        elif self.lock_type == 'spinlock':
            # Legacy spinlock - recommend qspinlock for most cases
            if self.subsystem in ['filesystem', 'ipc']:
                return 'qspinlock (cache/metadata) or sleeplock (I/O)'
            return 'qspinlock'
        return 'unknown'

class LockInventory:
    """Main lock inventory scanner"""
    def __init__(self, kernel_dir: str):
        self.kernel_dir = Path(kernel_dir)
        self.locks: Dict[str, LockInfo] = {}
        self.stats = defaultdict(int)

    def scan(self):
        """Scan entire kernel directory for locks"""
        print(f"Scanning {self.kernel_dir}...")

        # Find all .c and .h files
        c_files = list(self.kernel_dir.rglob("*.c"))
        h_files = list(self.kernel_dir.rglob("*.h"))
        all_files = c_files + h_files

        print(f"Found {len(all_files)} files to scan")

        for file_path in all_files:
            self._scan_file(file_path)

        # Second pass: find initialization and acquisition sites
        for file_path in all_files:
            self._scan_usage(file_path)

        self._compute_stats()

    def _scan_file(self, file_path: Path):
        """Scan a single file for lock declarations"""
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                lines = content.split('\n')

                for lock_type, pattern in LOCK_PATTERNS.items():
                    for match in re.finditer(pattern, content):
                        lock_name = match.group(1)
                        line_num = content[:match.start()].count('\n') + 1

                        # Create unique key for lock
                        rel_path = file_path.relative_to(self.kernel_dir)
                        lock_key = f"{rel_path}:{lock_name}"

                        if lock_key not in self.locks:
                            self.locks[lock_key] = LockInfo(
                                lock_name, lock_type, str(rel_path), line_num
                            )
        except Exception as e:
            print(f"Error scanning {file_path}: {e}")

    def _scan_usage(self, file_path: Path):
        """Scan file for lock initialization and usage patterns"""
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                rel_path = file_path.relative_to(self.kernel_dir)

                # Find initialization sites
                for init_type, pattern in INIT_PATTERNS.items():
                    for match in re.finditer(pattern, content):
                        lock_ref = match.group(1).strip()
                        line_num = content[:match.start()].count('\n') + 1

                        # Try to find corresponding lock
                        for lock_key, lock_info in self.locks.items():
                            if lock_info.name in lock_ref:
                                lock_info.init_sites.append(
                                    (str(rel_path), line_num, init_type)
                                )

                # Find acquisition sites
                for acq_type, pattern in ACQUIRE_PATTERNS.items():
                    for match in re.finditer(pattern, content):
                        lock_ref = match.group(1).strip()
                        line_num = content[:match.start()].count('\n') + 1

                        # Try to find corresponding lock
                        for lock_key, lock_info in self.locks.items():
                            if lock_info.name in lock_ref:
                                lock_info.acquire_sites.append(
                                    (str(rel_path), line_num, acq_type)
                                )
        except Exception as e:
            print(f"Error scanning usage in {file_path}: {e}")

    def _compute_stats(self):
        """Compute statistics about locks"""
        for lock_info in self.locks.values():
            self.stats[f'total_{lock_info.lock_type}'] += 1
            self.stats[f'subsys_{lock_info.subsystem}'] += 1
            self.stats[f'priority_{lock_info.priority}'] += 1

    def generate_report(self, output_file: str):
        """Generate comprehensive migration report"""
        with open(output_file, 'w') as f:
            self._write_header(f)
            self._write_summary(f)
            self._write_priority_matrix(f)
            self._write_detailed_inventory(f)
            self._write_migration_recommendations(f)

        print(f"\nReport written to {output_file}")

    def _write_header(self, f):
        """Write report header"""
        f.write("=" * 80 + "\n")
        f.write("ExoV6 Lock Migration Inventory Report\n")
        f.write("Phase 7.1: Automated Lock Analysis\n")
        f.write("=" * 80 + "\n\n")

    def _write_summary(self, f):
        """Write executive summary"""
        f.write("EXECUTIVE SUMMARY\n")
        f.write("-" * 80 + "\n\n")

        total_locks = len(self.locks)
        legacy_locks = sum(1 for l in self.locks.values()
                          if l.lock_type in ['spinlock', 'sleeplock'])
        modern_locks = total_locks - legacy_locks

        f.write(f"Total Locks Found:        {total_locks}\n")
        f.write(f"Legacy Locks (to migrate): {legacy_locks}\n")
        f.write(f"Modern Locks (migrated):   {modern_locks}\n")
        f.write(f"Migration Progress:        {modern_locks}/{total_locks} ")
        f.write(f"({100*modern_locks//total_locks if total_locks > 0 else 0}%)\n\n")

        f.write("Lock Type Breakdown:\n")
        for lock_type in ['spinlock', 'sleeplock', 'qspinlock',
                         'adaptive_mutex', 'lwkt_token']:
            count = self.stats.get(f'total_{lock_type}', 0)
            if count > 0:
                f.write(f"  {lock_type:20s}: {count:3d}\n")

        f.write("\n")

    def _write_priority_matrix(self, f):
        """Write priority matrix for migration planning"""
        f.write("MIGRATION PRIORITY MATRIX\n")
        f.write("-" * 80 + "\n\n")

        # Group locks by priority
        priority_groups = defaultdict(list)
        for lock_info in self.locks.values():
            if lock_info.lock_type in ['spinlock']:  # Only legacy spinlocks
                priority_groups[lock_info.priority].append(lock_info)

        priorities = ['P0-Critical', 'P1-High', 'P2-Medium', 'P3-Low', 'P3-Infrastructure']

        for priority in priorities:
            locks_in_priority = priority_groups[priority]
            if locks_in_priority:
                f.write(f"{priority}: {len(locks_in_priority)} locks\n")

                # Group by subsystem
                subsys_groups = defaultdict(list)
                for lock in locks_in_priority:
                    subsys_groups[lock.subsystem].append(lock)

                for subsys, locks in sorted(subsys_groups.items()):
                    f.write(f"  {subsys:15s}: {len(locks):2d} locks")
                    if subsys in ['sched', 'memory']:
                        f.write(" (COMPLETED in Phase 5)")
                    elif subsys in ['filesystem', 'device']:
                        f.write(" (PLANNED for Phase 7)")
                    f.write("\n")
                f.write("\n")

    def _write_detailed_inventory(self, f):
        """Write detailed lock-by-lock inventory"""
        f.write("DETAILED LOCK INVENTORY\n")
        f.write("-" * 80 + "\n\n")

        # Group by subsystem
        subsys_groups = defaultdict(list)
        for lock_info in self.locks.values():
            subsys_groups[lock_info.subsystem].append(lock_info)

        for subsys in sorted(subsys_groups.keys()):
            locks = subsys_groups[subsys]
            f.write(f"\n{'=' * 80}\n")
            f.write(f"Subsystem: {subsys.upper()} ({len(locks)} locks)\n")
            f.write(f"{'=' * 80}\n\n")

            for lock_info in sorted(locks, key=lambda x: x.name):
                f.write(f"Lock: {lock_info.name}\n")
                f.write(f"  Type:          {lock_info.lock_type}\n")
                f.write(f"  File:          {lock_info.file_path}:{lock_info.line_num}\n")
                f.write(f"  Priority:      {lock_info.priority}\n")
                f.write(f"  Recommended:   {lock_info.recommended_type}\n")

                if lock_info.init_sites:
                    f.write(f"  Init sites:    {len(lock_info.init_sites)}\n")
                    for site_file, site_line, init_type in lock_info.init_sites[:3]:
                        f.write(f"    - {site_file}:{site_line} ({init_type})\n")
                    if len(lock_info.init_sites) > 3:
                        f.write(f"    ... and {len(lock_info.init_sites)-3} more\n")

                if lock_info.acquire_sites:
                    f.write(f"  Usage sites:   {len(lock_info.acquire_sites)}\n")
                    for site_file, site_line, acq_type in lock_info.acquire_sites[:3]:
                        f.write(f"    - {site_file}:{site_line} ({acq_type})\n")
                    if len(lock_info.acquire_sites) > 3:
                        f.write(f"    ... and {len(lock_info.acquire_sites)-3} more\n")

                f.write("\n")

    def _write_migration_recommendations(self, f):
        """Write specific migration recommendations"""
        f.write("=" * 80 + "\n")
        f.write("MIGRATION RECOMMENDATIONS\n")
        f.write("=" * 80 + "\n\n")

        f.write("Phase 7.2 - P1 Filesystem Locks (Immediate Priority):\n")
        f.write("-" * 80 + "\n")

        fs_locks = [l for l in self.locks.values()
                   if l.subsystem == 'filesystem' and l.lock_type == 'spinlock']

        if fs_locks:
            for lock_info in fs_locks:
                f.write(f"\n{lock_info.name} ({lock_info.file_path}):\n")
                f.write(f"  Current:      {lock_info.lock_type}\n")
                f.write(f"  Recommended:  {lock_info.recommended_type}\n")
                f.write(f"  Migration:    ")

                if 'cache' in lock_info.name.lower():
                    f.write("qspinlock at LOCK_LEVEL_FILESYSTEM (cache protection)\n")
                    f.write(f"  sed -i 's/struct spinlock {lock_info.name}/")
                    f.write(f"struct qspinlock {lock_info.name}/g'\n")
                elif 'log' in lock_info.name.lower():
                    f.write("adaptive_mutex at LOCK_LEVEL_FILESYSTEM (log protection)\n")
                else:
                    f.write("qspinlock at LOCK_LEVEL_FILESYSTEM\n")
        else:
            f.write("  ✓ All filesystem locks already migrated!\n")

        f.write("\n\nPhase 7.3 - P2 Device Locks:\n")
        f.write("-" * 80 + "\n")

        dev_locks = [l for l in self.locks.values()
                    if l.subsystem == 'device' and l.lock_type == 'spinlock']

        if dev_locks:
            for lock_info in dev_locks:
                f.write(f"\n{lock_info.name} ({lock_info.file_path}):\n")
                f.write(f"  Recommended:  qspinlock at LOCK_LEVEL_DEVICE\n")
        else:
            f.write("  ✓ All device locks already migrated!\n")

        f.write("\n")

def main():
    """Main entry point"""
    if len(sys.argv) > 1:
        kernel_dir = sys.argv[1]
    else:
        # Default to ../kernel relative to script location
        script_dir = Path(__file__).parent
        kernel_dir = script_dir.parent / 'kernel'

    if not Path(kernel_dir).exists():
        print(f"Error: Kernel directory not found: {kernel_dir}")
        sys.exit(1)

    print("=" * 80)
    print("ExoV6 Lock Migration Inventory")
    print("Phase 7.1: Automated Analysis")
    print("=" * 80)
    print()

    inventory = LockInventory(kernel_dir)
    inventory.scan()

    output_file = "LOCK_MIGRATION_INVENTORY.txt"
    inventory.generate_report(output_file)

    print("\nInventory complete!")
    print(f"Total locks found: {len(inventory.locks)}")
    print(f"Report saved to: {output_file}")

if __name__ == '__main__':
    main()
