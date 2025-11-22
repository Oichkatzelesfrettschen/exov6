#!/bin/bash
set -e

# Setup stubs
mkdir -p kernel/test_stubs

# Stub hazard_pointer.h
echo "Creating stub kernel/test_stubs/hazard_pointer.h"
cat > kernel/test_stubs/hazard_pointer.h <<EOF
#pragma once
#include "lockfree.h"
EOF

# Stub rcu_pdac.h
echo "Creating stub kernel/test_stubs/rcu_pdac.h"
cat > kernel/test_stubs/rcu_pdac.h <<EOF
#pragma once
typedef struct { int dummy; } rcu_head_t;
typedef struct { int dummy; } rcu_state_t;
EOF

# Compile test
# -I kernel/test_stubs first to override include/
echo "Compiling test_minix3_stress..."
gcc -g -O0 \
    -I kernel/test_stubs -I include -I kernel -I kernel/include \
    kernel/test_minix3_stress.c \
    kernel/fs/minix3.c \
    kernel/vfs/vfs.c \
    kernel/buffer_cache.c \
    kernel/string.c \
    -o test_minix3 \
    -lpthread

echo "Compilation successful. Run ./test_minix3 to execute."
