#!/bin/bash
# Automated header fix script for FeuerBird Exokernel
# Implements the reorganization plan

set -e

PROJECT_ROOT="${1:-$(pwd)}"
cd "$PROJECT_ROOT"

echo "=== FeuerBird Exokernel Header Reorganization Script ==="
echo "Project root: $PROJECT_ROOT"
echo ""

# Create backup
echo "Creating backup..."
tar -czf header_backup_$(date +%Y%m%d_%H%M%S).tar.gz include/ kernel/*.h libos/*.h 2>/dev/null || true

# Step 1: Remove duplicate headers from include/ that belong in kernel/
echo "Step 1: Removing kernel-internal headers from include/..."

KERNEL_ONLY_HEADERS=(
    "spinlock.h" "sleeplock.h" "qspinlock.h" "rspinlock.h"
    "mmu.h" "mmu64.h" "trap.h" "traps.h" 
    "uart.h" "kbd.h" "lapic.h" "ioapic.h"
    "mp.h" "picirq.h" "console.h"
)

for header in "${KERNEL_ONLY_HEADERS[@]}"; do
    if [ -f "include/$header" ] && [ -f "kernel/$header" ]; then
        echo "  Removing include/$header (keeping kernel/$header)"
        rm -f "include/$header"
    fi
done

# Step 2: Fix exo.h duplication
echo "Step 2: Consolidating exo.h..."

if [ -f "kernel/exo.h" ] && [ -f "include/exo.h" ]; then
    echo "  Merging kernel/exo.h into include/exo.h"
    
    # Create merged version
    cat > include/exo_merged.h << 'EOF'
#ifndef FEUERBIRD_EXOKERNEL_EXO_H
#define FEUERBIRD_EXOKERNEL_EXO_H

/**
 * @file exo.h
 * @brief Unified exokernel interface
 * 
 * Consolidated from kernel/exo.h and include/exo.h
 * Pure C17 implementation
 */

#include <stdint.h>
#include <stddef.h>
#include "types.h"

/* Hash for capability authentication */
typedef struct hash256 {
    uint64_t parts[4];
} hash256_t;

/* Exokernel capability structure */
typedef struct exo_cap {
    uint32_t pa;         /* Physical address (if memory cap) */
    uint32_t id;         /* Resource identifier */
    uint32_t rights;     /* Rights bitmask */
    uint32_t owner;      /* Owner process/zone */
    hash256_t auth_tag;  /* Authentication tag */
} exo_cap;

/* Block device capability */
typedef struct exo_blockcap {
    uint32_t dev;        /* Device number */
    uint32_t blockno;    /* Block number */
    uint32_t rights;     /* Rights bitmask */
    uint32_t owner;      /* Owner process/zone */
} exo_blockcap;

/* Function declarations appropriate for include/ */
int exo_self_insert_pte(uint32_t vaddr, uint32_t pte);
int exo_self_unmap_page(uint32_t vaddr);
int exo_self_insert_pte_range(uint32_t vaddr, uint32_t *pte, size_t count);

/* Capability operations */
int cap_verify(exo_cap c);
exo_cap cap_new(uint32_t id, uint32_t rights, uint32_t owner);

/* IPC operations */
int exo_send(exo_cap dest, const void *msg, size_t len);
int exo_recv(exo_cap src, void *msg, size_t len);

/* Disk operations */
int exo_disk_read(exo_blockcap cap, void *buf);
int exo_disk_write(exo_blockcap cap, const void *buf);

#endif /* FEUERBIRD_EXOKERNEL_EXO_H */
EOF
    
    mv include/exo_merged.h include/exo.h
    rm -f kernel/exo.h
fi

# Step 3: Fix header guards
echo "Step 3: Standardizing header guards..."

fix_header_guard() {
    local file="$1"
    local zone="$2"
    local basename=$(basename "$file" .h)
    local guard="FEUERBIRD_EXOKERNEL_${zone}_${basename^^}_H"
    
    # Check if file has pragma once
    if grep -q "^#pragma once" "$file"; then
        echo "  Converting $file from pragma once to guards"
        
        # Create temp file with proper guards
        {
            echo "#ifndef $guard"
            echo "#define $guard"
            echo ""
            # Skip pragma once line and output rest
            grep -v "^#pragma once" "$file"
            echo ""
            echo "#endif /* $guard */"
        } > "${file}.tmp"
        
        mv "${file}.tmp" "$file"
    fi
}

# Fix guards in kernel headers
for header in kernel/*.h; do
    [ -f "$header" ] && fix_header_guard "$header" "KERNEL"
done

# Fix guards in libos headers
for header in libos/*.h; do
    [ -f "$header" ] && fix_header_guard "$header" "LIBOS"
done

# Step 4: Update include paths in source files
echo "Step 4: Updating include paths..."

# Fix includes that should reference kernel-internal headers
for src in kernel/*.c; do
    [ -f "$src" ] || continue
    
    # Update spinlock includes
    sed -i.bak 's|#include ["<]spinlock.h[">]|#include "spinlock.h"|g' "$src"
    sed -i.bak 's|#include ["<]sleeplock.h[">]|#include "sleeplock.h"|g' "$src"
    
    # Update driver includes
    sed -i.bak 's|#include ["<]uart.h[">]|#include "uart.h"|g' "$src"
    sed -i.bak 's|#include ["<]kbd.h[">]|#include "kbd.h"|g' "$src"
    
    # Clean up backup files
    rm -f "${src}.bak"
done

# Step 5: Create directory structure for future reorganization
echo "Step 5: Creating new directory structure..."

mkdir -p include/exo/api
mkdir -p kernel/include
mkdir -p kernel/internal
mkdir -p libos/include  
mkdir -p libos/internal
mkdir -p rump/include
mkdir -p rump/internal

# Step 6: Move obvious zone-specific headers
echo "Step 6: Moving zone-specific headers..."

# Move kernel internals
for header in proc.h sched.h vm.h; do
    if [ -f "kernel/$header" ]; then
        echo "  Moving kernel/$header to kernel/internal/"
        mv "kernel/$header" "kernel/internal/" 2>/dev/null || true
    fi
done

# Step 7: Generate migration report
echo "Step 7: Generating migration report..."

{
    echo "Header Migration Report"
    echo "======================"
    echo "Date: $(date)"
    echo ""
    echo "Headers removed from include/:"
    for header in "${KERNEL_ONLY_HEADERS[@]}"; do
        [ ! -f "include/$header" ] && echo "  - $header"
    done
    echo ""
    echo "Headers with fixed guards:"
    find kernel libos -name "*.h" -exec grep -l "^#ifndef FEUERBIRD_EXOKERNEL_" {} \; | wc -l
    echo ""
    echo "New directory structure created:"
    find . -type d -name "internal" -o -name "include" | grep -E "(kernel|libos|rump)" | sort
} > header_migration_report.txt

echo ""
echo "=== Header Fix Complete ==="
echo "Report saved to: header_migration_report.txt"
echo ""
echo "Next steps:"
echo "1. Review changes with: git diff"
echo "2. Test compilation: make clean && make kernel"
echo "3. Commit changes if successful"