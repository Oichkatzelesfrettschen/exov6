#!/bin/bash
# Comprehensive repository reorganization script
# Cleans up file structure, removes duplicates, and standardizes naming

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_success() { echo -e "${GREEN}[SUCCESS]${NC} $1"; }
log_warning() { echo -e "${YELLOW}[WARNING]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

# ============================================================================
# Phase 1: Clean Build Artifacts
# ============================================================================

clean_build_artifacts() {
    log_info "Cleaning build artifacts..."
    
    # Remove object files and dependencies
    find . -type f \( -name "*.o" -o -name "*.d" \) -delete
    
    # Remove assembly listings
    find . -type f -name "*.asm" -not -path "./tests/*" -delete
    
    # Remove temporary files
    rm -f *.tmp *.bak *.orig *~
    
    # Clean specific build files
    rm -f bootblock* entryother* initcode* kernel64 kernelmemfs*
    rm -f *.sym vectors.S
    
    # Keep essential images but remove duplicates
    rm -f xv6*.img kernelmemfs.img
    
    log_success "Build artifacts cleaned"
}

# ============================================================================
# Phase 2: Reorganize Root Directory
# ============================================================================

organize_root_files() {
    log_info "Organizing root directory files..."
    
    # Move stray headers to include/
    for file in caplib.h chan.h defs.h fs.h ipc.h param.h stat.h types.h user.h; do
        if [ -f "$file" ]; then
            log_info "  Moving $file -> include/"
            mv "$file" include/ 2>/dev/null || true
        fi
    done
    
    # Move duplicate headers
    rm -f "exo_cpu 3.h"  # Remove duplicate with space
    [ -f "exo_cpu.h" ] && mv exo_cpu.h include/
    [ -f "exo_stream.h" ] && mv exo_stream.h include/
    
    # Move boot files to kernel/boot/
    mkdir -p kernel/boot
    for file in boot_kernel.S bootasm_minimal.S entry_minimal.S; do
        if [ -f "$file" ]; then
            log_info "  Moving $file -> kernel/boot/"
            mv "$file" kernel/boot/
        fi
    done
    
    # Move test files to tests/
    mkdir -p tests/integration
    [ -f "integrate_tests.c" ] && mv integrate_tests.c tests/integration/
    [ -f "hello.c" ] && mv hello.c tests/examples/
    [ -f "hello_kernel.c" ] && mv hello_kernel.c tests/kernel/
    
    # Move shell files to user/shell/
    mkdir -p user/shell
    [ -f "shell_architecture.h" ] && mv shell_architecture.h user/shell/
    [ -f "shell_comprehensive.c" ] && mv shell_comprehensive.c user/shell/
    [ -f "shell_support.c" ] && mv shell_support.c user/shell/
    
    # Move mkfs to tools/
    mkdir -p tools
    [ -f "mkfs.c" ] && mv mkfs.c tools/
    [ -f "mkfs_standalone.c" ] && mv mkfs_standalone.c tools/
    
    # Move kernel stub
    [ -f "kernel_stub.c" ] && mv kernel_stub.c kernel/stubs/
    
    log_success "Root files organized"
}

# ============================================================================
# Phase 3: Deduplicate User Programs
# ============================================================================

deduplicate_user_programs() {
    log_info "Deduplicating user programs..."
    
    cd "$PROJECT_ROOT/user"
    
    # Create backup directory
    mkdir -p variants_backup
    
    # Process each utility with variants
    for base in cat echo pwd test sh ls wc true false; do
        if [ -f "${base}.c" ]; then
            # Find the most complete variant
            best="${base}.c"
            max_lines=$(wc -l < "${base}.c" 2>/dev/null || echo 0)
            
            for variant in ${base}_real.c ${base}_simple.c ${base}_working.c; do
                if [ -f "$variant" ]; then
                    lines=$(wc -l < "$variant")
                    if [ "$lines" -gt "$max_lines" ]; then
                        max_lines=$lines
                        best=$variant
                    fi
                    # Backup variant
                    mv "$variant" variants_backup/
                fi
            done
            
            # Use best implementation
            if [ "$best" != "${base}.c" ] && [ -f "variants_backup/$best" ]; then
                log_info "  Using $best as ${base}.c"
                mv "variants_backup/$best" "${base}.c"
            fi
        else
            # No base file, find best variant
            for variant in ${base}_real.c ${base}_simple.c ${base}_working.c; do
                if [ -f "$variant" ]; then
                    log_info "  Renaming $variant -> ${base}.c"
                    mv "$variant" "${base}.c"
                    break
                fi
            done
        fi
    done
    
    cd "$PROJECT_ROOT"
    log_success "User programs deduplicated"
}

# ============================================================================
# Phase 4: Organize Engine Directory
# ============================================================================

organize_engine_directory() {
    log_info "Merging engine directory..."
    
    if [ -d "engine" ]; then
        # Merge engine/kernel files
        if [ -d "engine/kernel" ]; then
            for file in engine/kernel/*.c engine/kernel/*.h engine/kernel/*.S; do
                if [ -f "$file" ]; then
                    basename=$(basename "$file")
                    if [ ! -f "kernel/$basename" ]; then
                        log_info "  Moving $file -> kernel/"
                        mv "$file" kernel/
                    else
                        log_warning "  Conflict: $basename exists, saving as ${basename%.c}_engine.c"
                        mv "$file" "kernel/${basename%.c}_engine${basename##*.}"
                    fi
                fi
            done
        fi
        
        # Merge engine/user files
        if [ -d "engine/user" ]; then
            cp -r engine/user/demos-tests/* demos/ 2>/dev/null || true
        fi
        
        # Remove empty engine directory
        rmdir engine/kernel engine/user engine 2>/dev/null || true
    fi
    
    log_success "Engine directory merged"
}

# ============================================================================
# Phase 5: Standardize File Names
# ============================================================================

standardize_filenames() {
    log_info "Standardizing file names..."
    
    # Remove .cpp23 and other weird extensions
    find . -name "*.cpp23" -exec bash -c 'mv "$0" "${0%.cpp23}.c"' {} \;
    find . -name "*.cpp" -exec bash -c 'mv "$0" "${0%.cpp}.c"' {} \;
    
    # Fix files with numbers in names
    for file in $(find . -name "*[0-9]*" -type f); do
        newname=$(echo "$file" | sed 's/[0-9]//g' | sed 's/__/_/g')
        if [ "$file" != "$newname" ] && [ ! -f "$newname" ]; then
            log_info "  Renaming $file -> $newname"
            mv "$file" "$newname"
        fi
    done
    
    # Remove _INFO style suffixes
    find . -name "*_INFO.*" -exec bash -c 'mv "$0" "${0/_INFO/}"' {} \;
    
    log_success "Filenames standardized"
}

# ============================================================================
# Phase 6: Create Standard Directory Structure
# ============================================================================

create_standard_structure() {
    log_info "Creating standard directory structure..."
    
    # Core directories
    mkdir -p kernel/{boot,drivers,fs,ipc,mem,sched,sync,sys}
    mkdir -p libos/{posix,pthread,signal,fs,mem}
    mkdir -p user/{bin,sbin,shell}
    mkdir -p include/{kernel,libos,sys}
    mkdir -p tools/{build,debug,test}
    mkdir -p tests/{unit,integration,posix,performance}
    mkdir -p docs/{api,design,guides}
    
    log_success "Standard structure created"
}

# ============================================================================
# Phase 7: Move Files to Proper Locations
# ============================================================================

organize_kernel_files() {
    log_info "Organizing kernel files by subsystem..."
    
    cd "$PROJECT_ROOT/kernel"
    
    # Boot subsystem
    mv -f boot*.c boot*.S entry*.S boot/ 2>/dev/null || true
    
    # Memory subsystem
    mv -f vm.c mmu*.c kalloc.c mem/ 2>/dev/null || true
    
    # File system
    mv -f fs.c bio.c log.c ide.c fs/ 2>/dev/null || true
    
    # IPC subsystem
    mv -f *ipc*.c fastipc.c endpoint.c chan*.c ipc/ 2>/dev/null || true
    
    # Scheduling
    mv -f sched.c proc.c *_sched.c sched/ 2>/dev/null || true
    
    # Synchronization
    mv -f *lock*.c rcu.c sync/ 2>/dev/null || true
    
    # System calls
    mv -f syscall.c sys*.c trap*.c sys/ 2>/dev/null || true
    
    # Drivers
    mv -f console.c kbd.c uart.c ioapic.c lapic.c picirq.c drivers/ 2>/dev/null || true
    
    cd "$PROJECT_ROOT"
    log_success "Kernel files organized"
}

organize_libos_files() {
    log_info "Organizing libos files..."
    
    cd "$PROJECT_ROOT/libos"
    
    # POSIX layer
    mv -f posix.c posix*.c posix/ 2>/dev/null || true
    
    # Threading
    mv -f pthread*.c pthread/ 2>/dev/null || true
    
    # Signals
    mv -f signal*.c signal/ 2>/dev/null || true
    
    # File system
    mv -f fs*.c file*.c fs/ 2>/dev/null || true
    
    # Memory
    mv -f memory.c mem*.c mem/ 2>/dev/null || true
    
    cd "$PROJECT_ROOT"
    log_success "LibOS files organized"
}

# ============================================================================
# Phase 8: Update Build Files
# ============================================================================

update_build_files() {
    log_info "Updating build configuration..."
    
    # Update CMakeLists.txt paths
    cat > "$PROJECT_ROOT/CMakeLists_update.cmake" << 'EOF'
# Updated paths after reorganization
set(KERNEL_SOURCES
    kernel/boot/bootmain.c
    kernel/mem/vm.c
    kernel/mem/kalloc.c
    kernel/mem/mmu64.c
    kernel/fs/fs.c
    kernel/fs/bio.c
    kernel/fs/log.c
    kernel/fs/ide.c
    kernel/ipc/exo_ipc.c
    kernel/ipc/fastipc.c
    kernel/ipc/endpoint.c
    kernel/sched/proc.c
    kernel/sched/sched.c
    kernel/sched/beatty_sched.c
    kernel/sched/dag_sched.c
    kernel/sync/spinlock.c
    kernel/sync/sleeplock.c
    kernel/sync/rcu.c
    kernel/sys/syscall.c
    kernel/sys/sysproc.c
    kernel/sys/sysfile.c
    kernel/sys/trap.c
    kernel/drivers/console.c
    kernel/drivers/uart.c
    kernel/drivers/kbd.c
    # ... add more as needed
)
EOF
    
    log_success "Build files updated"
}

# ============================================================================
# Phase 9: Generate Report
# ============================================================================

generate_report() {
    log_info "Generating reorganization report..."
    
    cat > "$PROJECT_ROOT/REORGANIZATION_REPORT.md" << EOF
# Repository Reorganization Report

Date: $(date)

## Changes Made

### 1. Build Artifacts Removed
- Removed $(find . -type f \( -name "*.o" -o -name "*.d" \) 2>/dev/null | wc -l) object files
- Cleaned temporary and backup files

### 2. Root Directory Cleaned
- Moved headers to include/
- Moved boot files to kernel/boot/
- Moved tools to tools/
- Moved tests to tests/

### 3. User Programs Deduplicated
- Consolidated variant implementations (_real, _simple, _working)
- Backed up variants to user/variants_backup/

### 4. Kernel Organization
\`\`\`
kernel/
├── boot/      # Boot code
├── drivers/   # Device drivers
├── fs/        # File system
├── ipc/       # Inter-process communication
├── mem/       # Memory management
├── sched/     # Scheduling
├── sync/      # Synchronization
└── sys/       # System calls
\`\`\`

### 5. LibOS Organization
\`\`\`
libos/
├── posix/     # POSIX API
├── pthread/   # Threading
├── signal/    # Signal handling
├── fs/        # File operations
└── mem/       # Memory operations
\`\`\`

## File Statistics

- Kernel files: $(find kernel -name "*.c" | wc -l) C files
- LibOS files: $(find libos -name "*.c" | wc -l) C files
- User programs: $(find user -name "*.c" | wc -l) C files
- Total headers: $(find include -name "*.h" | wc -l) headers

## Next Steps

1. Update CMakeLists.txt with new paths
2. Test build with reorganized structure
3. Update documentation to reflect new layout
4. Commit changes with detailed message
EOF
    
    log_success "Report generated: REORGANIZATION_REPORT.md"
}

# ============================================================================
# Main Execution
# ============================================================================

main() {
    echo "========================================="
    echo "Repository Reorganization Script"
    echo "========================================="
    echo
    
    cd "$PROJECT_ROOT"
    
    # Confirmation
    echo "This script will:"
    echo "  1. Clean all build artifacts"
    echo "  2. Reorganize directory structure"
    echo "  3. Deduplicate files"
    echo "  4. Standardize naming conventions"
    echo "  5. Update build configuration"
    echo
    read -p "Continue? (y/N): " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        log_info "Reorganization cancelled"
        exit 0
    fi
    
    # Create backup
    log_info "Creating backup..."
    tar -czf "../exov6_backup_$(date +%Y%m%d_%H%M%S).tar.gz" . \
        --exclude=".git" --exclude="build" --exclude="*.o"
    
    # Execute phases
    clean_build_artifacts
    organize_root_files
    deduplicate_user_programs
    organize_engine_directory
    standardize_filenames
    create_standard_structure
    organize_kernel_files
    organize_libos_files
    update_build_files
    generate_report
    
    echo
    echo "========================================="
    log_success "Reorganization completed!"
    echo "========================================="
    echo
    echo "Review REORGANIZATION_REPORT.md for details"
    echo "Backup created in parent directory"
    echo
    echo "Next steps:"
    echo "  1. Review changes with: git status"
    echo "  2. Test build: mkdir build && cd build && cmake .. && make"
    echo "  3. Commit if successful: git add -A && git commit -m 'Reorganize repository structure'"
}

# Run if not sourced
if [ "${BASH_SOURCE[0]}" == "${0}" ]; then
    main "$@"
fi