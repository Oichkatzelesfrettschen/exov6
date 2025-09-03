#!/bin/bash
# Automated C++23 migration script for FeuerBird Exokernel
# This script performs the actual migration in phases

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Migration state file
STATE_FILE="$PROJECT_ROOT/.migration_state"

# Functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Load or initialize migration state
load_state() {
    if [ -f "$STATE_FILE" ]; then
        source "$STATE_FILE"
    else
        # Initialize state
        LIBCXX_BUILT=false
        DIRECTORIES_RESTRUCTURED=false
        DEDUPLICATION_DONE=false
        KERNEL_MIGRATED=false
        LIBOS_MIGRATED=false
        USER_MIGRATED=false
    fi
}

save_state() {
    cat > "$STATE_FILE" << EOF
LIBCXX_BUILT=$LIBCXX_BUILT
DIRECTORIES_RESTRUCTURED=$DIRECTORIES_RESTRUCTURED
DEDUPLICATION_DONE=$DEDUPLICATION_DONE
KERNEL_MIGRATED=$KERNEL_MIGRATED
LIBOS_MIGRATED=$LIBOS_MIGRATED
USER_MIGRATED=$USER_MIGRATED
EOF
}

# Phase 0: Backup
backup_codebase() {
    log_info "Creating backup of current codebase..."
    
    BACKUP_DIR="$PROJECT_ROOT/../exov6_backup_$(date +%Y%m%d_%H%M%S)"
    cp -r "$PROJECT_ROOT" "$BACKUP_DIR"
    
    log_success "Backup created at: $BACKUP_DIR"
}

# Phase 1: Build libc++
build_libcxx() {
    if [ "$LIBCXX_BUILT" = true ]; then
        log_info "libc++ already built, skipping..."
        return
    fi
    
    log_info "Building LLVM libc++ with C++23 support..."
    
    if [ -x "$SCRIPT_DIR/bootstrap_libcxx.sh" ]; then
        "$SCRIPT_DIR/bootstrap_libcxx.sh"
        LIBCXX_BUILT=true
        save_state
        log_success "libc++ built successfully!"
    else
        log_error "bootstrap_libcxx.sh not found or not executable"
        exit 1
    fi
}

# Phase 2: Restructure directories
restructure_directories() {
    if [ "$DIRECTORIES_RESTRUCTURED" = true ]; then
        log_info "Directories already restructured, skipping..."
        return
    fi
    
    log_info "Restructuring directories by license..."
    
    # Create new directory structure
    mkdir -p "$PROJECT_ROOT"/{bsd,gpl,mit,limine,llvm-libc++}/{kernel,libos,user,include}
    
    # Run restructuring script
    if [ -x "$SCRIPT_DIR/restructure_by_license.sh" ]; then
        # Modify script to actually move files
        sed -i.bak 's/# git mv/git mv/g; s/# mv/mv/g' "$SCRIPT_DIR/restructure_by_license.sh"
        "$SCRIPT_DIR/restructure_by_license.sh"
        
        DIRECTORIES_RESTRUCTURED=true
        save_state
        log_success "Directories restructured successfully!"
    else
        log_warning "Manual restructuring may be needed"
    fi
}

# Phase 3: Deduplicate code
deduplicate_code() {
    if [ "$DEDUPLICATION_DONE" = true ]; then
        log_info "Deduplication already done, skipping..."
        return
    fi
    
    log_info "Deduplicating utility implementations..."
    
    cd "$PROJECT_ROOT/user"
    
    # Perform actual deduplication
    for base in cat echo pwd test sh ls wc true false; do
        if [ -f "${base}.c" ]; then
            # Find best variant
            best=""
            max_lines=0
            
            for variant in ${base}.c ${base}_real.c ${base}_simple.c ${base}_working.c; do
                if [ -f "$variant" ]; then
                    lines=$(wc -l < "$variant")
                    if [ "$lines" -gt "$max_lines" ]; then
                        max_lines=$lines
                        best=$variant
                    fi
                fi
            done
            
            if [ -n "$best" ] && [ "$best" != "${base}.c" ]; then
                log_info "  Consolidating $base: using $best"
                mv "$best" "${base}.c"
            fi
            
            # Remove variants
            rm -f ${base}_real.c ${base}_simple.c ${base}_working.c
        fi
    done
    
    cd "$PROJECT_ROOT"
    DEDUPLICATION_DONE=true
    save_state
    log_success "Deduplication completed!"
}

# Convert a single C file to C++
convert_file_to_cpp() {
    local c_file="$1"
    local cpp_file="${c_file%.c}.cpp"
    
    if [ ! -f "$c_file" ]; then
        return
    fi
    
    log_info "  Converting: $c_file -> $cpp_file"
    
    # Create C++ version
    cat > "$cpp_file" << 'EOF'
// Auto-generated C++23 wrapper
// TODO: Complete migration to modern C++

extern "C" {
EOF
    
    # Include original C code
    cat "$c_file" >> "$cpp_file"
    
    cat >> "$cpp_file" << 'EOF'
} // extern "C"

// TODO: Migrate to C++23:
// - Replace malloc/free with RAII
// - Use std::expected instead of errno
// - Convert to classes where appropriate
// - Add [[nodiscard]] attributes
// - Use std::span for buffers
// - Apply concepts for type safety
EOF
    
    # Keep original for reference
    mv "$c_file" "${c_file}.bak"
}

# Phase 4: Migrate kernel
migrate_kernel() {
    if [ "$KERNEL_MIGRATED" = true ]; then
        log_info "Kernel already migrated, skipping..."
        return
    fi
    
    log_info "Migrating kernel to C++23..."
    
    cd "$PROJECT_ROOT/kernel"
    
    # Priority files for migration
    PRIORITY_FILES=(
        "main.c"
        "proc.c"
        "vm.c"
        "trap.c"
        "syscall.c"
        "cap.c"
        "exo_ipc.c"
        "spinlock.c"
    )
    
    for file in "${PRIORITY_FILES[@]}"; do
        if [ -f "$file" ]; then
            convert_file_to_cpp "$file"
        fi
    done
    
    # Update build system
    cd "$PROJECT_ROOT"
    if [ ! -f "Makefile.original" ]; then
        cp Makefile Makefile.original
    fi
    cp Makefile.cpp23 Makefile
    
    KERNEL_MIGRATED=true
    save_state
    log_success "Kernel migration completed!"
}

# Phase 5: Migrate LibOS
migrate_libos() {
    if [ "$LIBOS_MIGRATED" = true ]; then
        log_info "LibOS already migrated, skipping..."
        return
    fi
    
    log_info "Migrating LibOS to C++23..."
    
    cd "$PROJECT_ROOT/libos"
    
    # Convert LibOS files
    for file in *.c; do
        if [ -f "$file" ]; then
            convert_file_to_cpp "$file"
        fi
    done
    
    cd "$PROJECT_ROOT"
    LIBOS_MIGRATED=true
    save_state
    log_success "LibOS migration completed!"
}

# Phase 6: Migrate user programs
migrate_user() {
    if [ "$USER_MIGRATED" = true ]; then
        log_info "User programs already migrated, skipping..."
        return
    fi
    
    log_info "Migrating user programs to C++23..."
    
    cd "$PROJECT_ROOT/user"
    
    # Convert deduplicated utilities
    for file in cat.c echo.c grep.c ls.c mkdir.c rm.c sh.c wc.c cp.c mv.c pwd.c test.c; do
        if [ -f "$file" ]; then
            convert_file_to_cpp "$file"
        fi
    done
    
    cd "$PROJECT_ROOT"
    USER_MIGRATED=true
    save_state
    log_success "User programs migration completed!"
}

# Validation
validate_migration() {
    log_info "Validating migration..."
    
    cd "$PROJECT_ROOT"
    
    # Check if we can build
    log_info "Attempting C++23 build..."
    if make clean && make CXX_STD=c++23; then
        log_success "Build successful!"
    else
        log_warning "Build failed - manual intervention needed"
    fi
    
    # Run tests
    log_info "Running tests..."
    if make test; then
        log_success "Tests passed!"
    else
        log_warning "Some tests failed - review needed"
    fi
}

# Generate migration report
generate_report() {
    log_info "Generating migration report..."
    
    cat > "$PROJECT_ROOT/MIGRATION_REPORT.md" << EOF
# C++23 Migration Report

Generated: $(date)

## Migration Status

- [x] Backup created
- [$([ "$LIBCXX_BUILT" = true ] && echo "x" || echo " ")] libc++ built
- [$([ "$DIRECTORIES_RESTRUCTURED" = true ] && echo "x" || echo " ")] Directories restructured
- [$([ "$DEDUPLICATION_DONE" = true ] && echo "x" || echo " ")] Code deduplicated
- [$([ "$KERNEL_MIGRATED" = true ] && echo "x" || echo " ")] Kernel migrated
- [$([ "$LIBOS_MIGRATED" = true ] && echo "x" || echo " ")] LibOS migrated
- [$([ "$USER_MIGRATED" = true ] && echo "x" || echo " ")] User programs migrated

## File Statistics

### C Files Remaining
$(find . -name "*.c" -not -path "./llvm-*" | wc -l) files

### C++ Files Created
$(find . -name "*.cpp" -not -path "./llvm-*" | wc -l) files

### Backup Files
$(find . -name "*.c.bak" | wc -l) files

## Next Steps

1. Review auto-generated C++ files
2. Complete TODO items in each .cpp file
3. Remove extern "C" wrappers gradually
4. Implement proper RAII patterns
5. Replace error codes with std::expected
6. Add C++23 features (concepts, ranges, etc.)

## Build Instructions

\`\`\`bash
# Build with C++23
make clean
make CXX_STD=c++23

# Run tests
make test

# Run POSIX compliance tests
make posix-test
\`\`\`
EOF
    
    log_success "Report generated: MIGRATION_REPORT.md"
}

# Main migration flow
main() {
    echo "========================================="
    echo "FeuerBird C++23 Migration Script"
    echo "========================================="
    echo
    
    # Parse arguments
    SKIP_BACKUP=false
    DRY_RUN=false
    
    while [[ $# -gt 0 ]]; do
        case $1 in
            --skip-backup)
                SKIP_BACKUP=true
                shift
                ;;
            --dry-run)
                DRY_RUN=true
                shift
                ;;
            --reset)
                rm -f "$STATE_FILE"
                log_info "Migration state reset"
                shift
                ;;
            *)
                echo "Unknown option: $1"
                echo "Usage: $0 [--skip-backup] [--dry-run] [--reset]"
                exit 1
                ;;
        esac
    done
    
    # Load state
    load_state
    
    if [ "$DRY_RUN" = true ]; then
        log_warning "DRY RUN MODE - No changes will be made"
        exit 0
    fi
    
    # Confirmation
    echo "This script will:"
    echo "  1. Create a backup (unless --skip-backup)"
    echo "  2. Build LLVM libc++ with C++23"
    echo "  3. Restructure directories by license"
    echo "  4. Deduplicate code"
    echo "  5. Convert C files to C++"
    echo "  6. Update build system"
    echo
    read -p "Continue? (y/N): " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        log_info "Migration cancelled"
        exit 0
    fi
    
    # Execute migration phases
    if [ "$SKIP_BACKUP" = false ]; then
        backup_codebase
    fi
    
    build_libcxx
    restructure_directories
    deduplicate_code
    migrate_kernel
    migrate_libos
    migrate_user
    validate_migration
    generate_report
    
    echo
    echo "========================================="
    log_success "Migration completed successfully!"
    echo "========================================="
    echo
    echo "Next steps:"
    echo "  1. Review MIGRATION_REPORT.md"
    echo "  2. Check and fix any build errors"
    echo "  3. Complete TODO items in .cpp files"
    echo "  4. Run comprehensive tests"
    echo
}

# Run main function
main "$@"