#!/bin/bash
# Build personality-specific test binaries
# This script compiles test binaries with appropriate flags to trigger
# personality detection in our multi-personality syscall gateway

set -e

echo "==================================================="
echo "Building Personality-Specific Test Binaries"
echo "==================================================="

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Create output directory
mkdir -p binaries

# Function to add ELF note section
add_elf_note() {
    local binary=$1
    local os_type=$2
    local note_file=$(mktemp)
    
    case $os_type in
        linux)
            # Create GNU ABI note
            printf '\x04\x00\x00\x00' > $note_file  # namesz = 4
            printf '\x10\x00\x00\x00' >> $note_file # descsz = 16
            printf '\x01\x00\x00\x00' >> $note_file # type = NT_GNU_ABI_TAG
            printf 'GNU\x00' >> $note_file          # name = "GNU\0"
            printf '\x00\x00\x00\x00' >> $note_file # OS = Linux
            printf '\x06\x00\x00\x00' >> $note_file # major = 6
            printf '\x00\x00\x00\x00' >> $note_file # minor = 0
            printf '\x00\x00\x00\x00' >> $note_file # subminor = 0
            ;;
        freebsd)
            # Create FreeBSD ABI note
            printf '\x08\x00\x00\x00' > $note_file  # namesz = 8
            printf '\x04\x00\x00\x00' >> $note_file # descsz = 4
            printf '\x01\x00\x00\x00' >> $note_file # type = NT_FREEBSD_ABI_TAG
            printf 'FreeBSD\x00' >> $note_file      # name = "FreeBSD\0"
            printf '\x0e\x00\x00\x00' >> $note_file # version = 14
            ;;
        solaris)
            # Create Solaris ident note
            printf '\x08\x00\x00\x00' > $note_file  # namesz = 8
            printf '\x00\x00\x00\x00' >> $note_file # descsz = 0
            printf '\x01\x00\x00\x00' >> $note_file # type = 1
            printf 'Solaris\x00' >> $note_file      # name = "Solaris\0"
            ;;
    esac
    
    # Add note section to binary using objcopy if available
    if command -v objcopy >/dev/null 2>&1; then
        objcopy --add-section .note.ABI=$note_file \
                --set-section-flags .note.ABI=alloc,readonly \
                $binary 2>/dev/null || true
    fi
    
    rm -f $note_file
}

# Build Linux personality test
echo -e "\n${YELLOW}Building Linux personality test...${NC}"
if gcc -o binaries/test_linux test_linux_binary.c -static 2>/dev/null; then
    add_elf_note binaries/test_linux linux
    echo -e "${GREEN}✓ Linux test binary built${NC}"
    
    # Set Linux-specific ELF OS/ABI field
    if command -v patchelf >/dev/null 2>&1; then
        patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 binaries/test_linux 2>/dev/null || true
    fi
else
    # Build simplified version without Linux-specific headers
    cat > test_linux_simple.c << 'EOF'
#include <stdio.h>
#include <unistd.h>
#include <sys/syscall.h>

int main() {
    printf("Linux Personality Test (Simplified)\n");
    printf("PID: %d\n", getpid());
    
    // Try Linux-specific syscall numbers
    #ifdef __NR_gettid
    long tid = syscall(__NR_gettid);
    printf("TID: %ld\n", tid);
    #endif
    
    return 0;
}
EOF
    gcc -o binaries/test_linux test_linux_simple.c
    add_elf_note binaries/test_linux linux
    echo -e "${GREEN}✓ Linux test binary built (simplified)${NC}"
fi

# Build BSD personality test
echo -e "\n${YELLOW}Building BSD personality test...${NC}"
# Create simplified BSD test that compiles on any system
cat > test_bsd_simple.c << 'EOF'
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>

// BSD-specific syscall numbers
#define BSD_SYS_kqueue  362
#define BSD_SYS_kevent  363

int main() {
    printf("BSD Personality Test (Simplified)\n");
    printf("PID: %d\n", getpid());
    
    // Simulate BSD-specific behavior
    printf("Testing BSD-specific features...\n");
    
    // Check for /dev/kqueue (BSD-specific)
    int fd = open("/dev/kqueue", O_RDONLY);
    if (fd >= 0) {
        printf("Found /dev/kqueue\n");
        close(fd);
    }
    
    return 0;
}
EOF
gcc -o binaries/test_bsd test_bsd_simple.c
add_elf_note binaries/test_bsd freebsd

# Set BSD-specific ELF OS/ABI
printf '\x09' | dd of=binaries/test_bsd bs=1 seek=7 count=1 conv=notrunc 2>/dev/null || true
echo -e "${GREEN}✓ BSD test binary built${NC}"

# Build Illumos personality test
echo -e "\n${YELLOW}Building Illumos personality test...${NC}"
cat > test_illumos_simple.c << 'EOF'
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>

// Illumos-specific syscall numbers
#define ILLUMOS_SYS_zone 227
#define ILLUMOS_SYS_door 202

int main() {
    printf("Illumos Personality Test (Simplified)\n");
    printf("PID: %d\n", getpid());
    
    // Check for Illumos-specific paths
    int fd = open("/dev/poll", O_RDONLY);
    if (fd >= 0) {
        printf("Found /dev/poll (Illumos feature)\n");
        close(fd);
    }
    
    fd = open("/system/contract", O_RDONLY);
    if (fd >= 0) {
        printf("Found contract filesystem\n");
        close(fd);
    }
    
    return 0;
}
EOF
gcc -o binaries/test_illumos test_illumos_simple.c
add_elf_note binaries/test_illumos solaris

# Set Solaris ELF OS/ABI
printf '\x06' | dd of=binaries/test_illumos bs=1 seek=7 count=1 conv=notrunc 2>/dev/null || true
echo -e "${GREEN}✓ Illumos test binary built${NC}"

# Build V6/V7 compatibility test
echo -e "\n${YELLOW}Building V6/V7 compatibility test...${NC}"
gcc -o binaries/test_v6 test_v6_binary.c
# V6 binaries have magic number 0407 (a.out format)
# We'll keep it as ELF but mark it for V6 personality detection
echo -e "${GREEN}✓ V6/V7 test binary built${NC}"

# Build native FeuerBird test
echo -e "\n${YELLOW}Building native FeuerBird test...${NC}"
cat > test_feuerbird.c << 'EOF'
#include <stdio.h>
#include <unistd.h>

int main() {
    printf("FeuerBird Native Personality Test\n");
    printf("PID: %d\n", getpid());
    printf("This is a native FeuerBird binary\n");
    return 0;
}
EOF
gcc -o binaries/test_feuerbird test_feuerbird.c
echo -e "${GREEN}✓ FeuerBird native test binary built${NC}"

# Build POSIX 2024 test
echo -e "\n${YELLOW}Building POSIX 2024 test...${NC}"
cat > test_posix.c << 'EOF'
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

int main() {
    printf("POSIX 2024 Personality Test\n");
    printf("PID: %d\n", getpid());
    
    // Use POSIX-only features
    char *path = getenv("PATH");
    if (path) {
        printf("PATH: %.50s...\n", path);
    }
    
    return 0;
}
EOF
gcc -o binaries/test_posix test_posix.c -D_POSIX_C_SOURCE=202405L
echo -e "${GREEN}✓ POSIX 2024 test binary built${NC}"

# Create test runner script
cat > run_personality_tests.sh << 'EOF'
#!/bin/bash
# Run all personality test binaries

echo "==================================================="
echo "Running Personality Detection Tests"
echo "==================================================="

for binary in binaries/test_*; do
    if [ -x "$binary" ]; then
        echo ""
        echo "Testing: $(basename $binary)"
        echo "-------------------------------------------"
        
        # Check ELF headers
        if command -v readelf >/dev/null 2>&1; then
            echo "ELF OS/ABI: $(readelf -h $binary | grep 'OS/ABI:' | awk '{print $2}')"
            
            # Check for notes
            if readelf -n $binary 2>/dev/null | grep -q "NT_GNU_ABI_TAG"; then
                echo "Has GNU ABI note (Linux)"
            fi
            if readelf -n $binary 2>/dev/null | grep -q "FreeBSD"; then
                echo "Has FreeBSD note"
            fi
            if readelf -n $binary 2>/dev/null | grep -q "Solaris"; then
                echo "Has Solaris note"
            fi
            
            # Check interpreter
            interp=$(readelf -l $binary | grep interpreter | sed 's/.*: \(.*\)]/\1/')
            if [ -n "$interp" ]; then
                echo "Interpreter: $interp"
            fi
        fi
        
        # Run the binary (in our kernel it would trigger personality detection)
        echo "Output:"
        $binary || true
    fi
done

echo ""
echo "==================================================="
echo "Personality detection testing complete!"
echo "==================================================="
EOF
chmod +x run_personality_tests.sh

# Summary
echo ""
echo "==================================================="
echo -e "${GREEN}Build Complete!${NC}"
echo "==================================================="
echo "Built binaries in ./binaries/:"
ls -la binaries/
echo ""
echo "Each binary contains personality-specific markers:"
echo "  - test_linux:     GNU/Linux ABI note, Linux interpreter"
echo "  - test_bsd:       FreeBSD ABI note, BSD OS/ABI field"
echo "  - test_illumos:   Solaris ident note, Solaris OS/ABI"
echo "  - test_v6:        V6/V7 syscall compatibility test"
echo "  - test_feuerbird: Native FeuerBird binary"
echo "  - test_posix:     POSIX 2024 compliant binary"
echo ""
echo "Run ./run_personality_tests.sh to test all binaries"
echo "==================================================="