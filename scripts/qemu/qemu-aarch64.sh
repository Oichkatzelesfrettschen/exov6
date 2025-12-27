#!/usr/bin/env bash
set -euo pipefail
# Run FeuerBird for AArch64 under QEMU
QEMU=${QEMU:-qemu-system-aarch64}
KERNEL=${KERNEL:-kernel-aarch64}
exec "$QEMU" -M virt -cpu cortex-a53 -nographic -kernel "$KERNEL" -append "console=ttyAMA0"
