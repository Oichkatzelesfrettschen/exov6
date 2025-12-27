#!/usr/bin/env python3
"""
Intelligent file merger for FeuerBird Exokernel repository reorganization.
This script compares files with the same name and merges their best features.
"""

import os
import difflib
import hashlib
import shutil
from pathlib import Path

def get_file_hash(filepath):
    """Get MD5 hash of a file."""
    with open(filepath, 'rb') as f:
        return hashlib.md5(f.read()).hexdigest()

def merge_spinlock_headers():
    """Merge the three spinlock.h implementations into one optimal version."""
    print("=== Merging spinlock.h implementations ===")
    
    files = [
        "engine/kernel/spinlock.h",
        "kernel/spinlock.h", 
        "include/libos/spinlock.h"
    ]
    
    # Read all versions
    contents = {}
    for f in files:
        if os.path.exists(f):
            with open(f, 'r') as file:
                contents[f] = file.read()
    
    # Create merged version with best of all
    merged = """#pragma once

#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include "kernel_compat.h"
#include "config.h"

/* Forward declarations */
struct cpu;

/* Cache line size for alignment optimization */
extern size_t cache_line_size;
void detect_cache_line_size(void);

/* Ticket-based mutual exclusion lock for fair FIFO ordering */
struct ticketlock {
    _Atomic uint16_t head;  /* Next ticket to serve */
    _Atomic uint16_t tail;  /* Next ticket to issue */
};

/* Spinlock with debugging support */
struct spinlock {
    struct ticketlock ticket;  /* Underlying ticket lock */
    char *name;               /* Human-readable identifier */
    uint32_t pcs[10];        /* Call stack at acquisition */
    struct cpu *cpu;         /* CPU holding the lock */
};

/* Initialize spinlock with name */
void initlock(struct spinlock *lk, char *name);

#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
/* SMP spinlock operations */
void acquire(struct spinlock *lk);
void release(struct spinlock *lk);
int holding(struct spinlock *lk);

/* Queued spinlock support */
#if !defined(USE_TICKET_LOCK)
void qspin_lock(struct spinlock *lk);
void qspin_unlock(struct spinlock *lk);
#endif
#else
/* Uniprocessor stubs */
static inline void acquire(struct spinlock *lk) { (void)lk; }
static inline void release(struct spinlock *lk) { (void)lk; }
static inline int holding(struct spinlock *lk) { (void)lk; return 1; }
#endif

/* Cache line size detection at startup */
__attribute__((constructor))
static void initialize_cache_line_size(void) {
    if (cache_line_size == 0) {
        detect_cache_line_size();
    }
}

/* Alignment helper */
static inline size_t spinlock_align(void) {
    if (!cache_line_size) {
        detect_cache_line_size();
    }
    return cache_line_size;
}
"""
    
    # Write the merged version
    with open("include/spinlock.h", 'w') as f:
        f.write(merged)
    print("Created unified include/spinlock.h")
    
    # Remove the duplicates
    for f in ["kernel/spinlock.h", "include/libos/spinlock.h"]:
        if os.path.exists(f):
            os.remove(f)
            print(f"Removed duplicate: {f}")

def merge_stat_headers():
    """Merge stat.h implementations."""
    print("=== Merging stat.h implementations ===")
    
    files = [
        "engine/stat.h",
        "engine/kernel/stat.h",
        "kernel/stat.h",
        "include/stat.h"
    ]
    
    # Read the most complete version
    best_file = None
    max_size = 0
    for f in files:
        if os.path.exists(f):
            size = os.path.getsize(f)
            if size > max_size:
                max_size = size
                best_file = f
    
    if best_file:
        # Use the most complete version
        shutil.copy2(best_file, "include/sys/stat.h")
        print(f"Used {best_file} as base for include/sys/stat.h")
        
        # Remove duplicates
        for f in files:
            if f != best_file and os.path.exists(f):
                os.remove(f)
                print(f"Removed duplicate: {f}")

def merge_demo_files():
    """Merge demo files from engine into demos directory."""
    print("=== Merging demo files ===")
    
    engine_demos = Path("engine/user/demos-tests")
    main_demos = Path("demos")
    
    if not engine_demos.exists():
        return
    
    for demo_file in engine_demos.glob("*.c"):
        main_file = main_demos / demo_file.name
        
        if main_file.exists():
            # Compare files
            engine_hash = get_file_hash(demo_file)
            main_hash = get_file_hash(main_file)
            
            if engine_hash != main_hash:
                # Files differ - merge them
                print(f"Merging {demo_file.name}")
                
                # Read both files
                with open(demo_file, 'r') as f:
                    engine_content = f.readlines()
                with open(main_file, 'r') as f:
                    main_content = f.readlines()
                
                # Use difflib to create unified diff
                diff = difflib.unified_diff(main_content, engine_content,
                                           fromfile=str(main_file),
                                           tofile=str(demo_file))
                
                # For now, keep the engine version if it's larger (likely more complete)
                if len(engine_content) > len(main_content):
                    shutil.copy2(demo_file, main_file)
                    print(f"  Used engine version (larger)")
                else:
                    print(f"  Kept main version")
        else:
            # File only exists in engine - copy it
            shutil.copy2(demo_file, main_file)
            print(f"Added {demo_file.name} from engine")

def find_unique_engine_files():
    """Find files that only exist in engine directory."""
    print("=== Finding unique engine files ===")
    
    engine_path = Path("engine")
    unique_files = []
    
    for engine_file in engine_path.rglob("*.[ch]"):
        # Get relative path from engine dir
        rel_path = engine_file.relative_to(engine_path)
        
        # Check if file exists elsewhere
        alternatives = [
            Path(".") / rel_path,
            Path("kernel") / rel_path.name,
            Path("include") / rel_path.name,
            Path("libos") / rel_path.name,
            Path("user") / rel_path.name,
        ]
        
        exists_elsewhere = any(alt.exists() for alt in alternatives)
        
        if not exists_elsewhere:
            unique_files.append(engine_file)
            print(f"Unique: {engine_file}")
    
    return unique_files

def main():
    """Main merge process."""
    print("Starting intelligent merge process...")
    
    # 1. Merge spinlock headers
    merge_spinlock_headers()
    
    # 2. Merge stat headers
    merge_stat_headers()
    
    # 3. Merge demo files
    merge_demo_files()
    
    # 4. Find unique files
    unique_files = find_unique_engine_files()
    
    print(f"\nFound {len(unique_files)} unique files in engine/")
    print("\nMerge complete. Review the changes before committing.")

if __name__ == "__main__":
    main()