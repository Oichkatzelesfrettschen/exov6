# QEMU Boot Status

## Current State (January 2025)

The FeuerBird kernel builds successfully as a 64-bit ELF executable but does not
boot directly in QEMU using the `-kernel` flag.

### Error Message

```
qemu-system-x86_64: Error loading uncompressed kernel without PVH ELF Note
```

### Root Cause

1. **Architecture mismatch**: The kernel is compiled as x86_64 (64-bit), but the
   multiboot entry code in `kernel/boot/entry.S` is 32-bit (`.code32`).

2. **Missing long mode transition**: Multiboot 1 specification assumes 32-bit
   protected mode entry. A 64-bit kernel requires additional boot code to:
   - Set up a GDT with 64-bit segments
   - Enable PAE and long mode
   - Set up initial page tables
   - Jump to 64-bit code

3. **PVH note**: QEMU's direct kernel loading for 64-bit ELF requires a PVH
   (Para-Virtualized Hardware) ELF note, which is not present.

## Boot Files Inventory

| File | Purpose | Status |
|------|---------|--------|
| `kernel/boot/entry.S` | 32-bit multiboot entry | Excluded (conflicts with 64-bit) |
| `kernel/boot/bootasm.S` | BIOS boot block | Excluded |
| `kernel/boot/bootmain.c` | Boot loader main | Excluded |
| `kernel/boot/main64.c` | 64-bit main stub | Present but minimal |
| `kernel/swtch64.S` | 64-bit context switch | **Active** |

## Solutions (Roadmap)

### Option 1: Multiboot2 Support (Recommended)

Multiboot2 supports 64-bit ELF directly. Requires:
- Adding multiboot2 header to assembly
- Using QEMU with GRUB2 bootloader
- Updating linker script

### Option 2: 32-to-64 Trampoline

Keep multiboot1 compatibility by:
- Adding 32-bit protected mode stub
- Implementing long mode transition code
- Setting up identity-mapped page tables for initial boot

### Option 3: UEFI Boot

Use UEFI boot path instead of legacy BIOS/multiboot:
- Requires building as PE/COFF or using UEFI stub loader
- Most complex but most modern approach

### Option 4: Use GRUB2 Directly

Boot via GRUB2 instead of QEMU's `-kernel`:
```bash
# Create bootable disk image
grub-mkrescue -o feuerbird.iso iso/

# Boot with QEMU
qemu-system-x86_64 -cdrom feuerbird.iso
```

## Current Workaround

For development testing, use the kernel in a full system image with GRUB2,
or test individual components with the userspace build targets.

## Verification

To verify the kernel binary is correctly formatted:

```bash
# Check ELF format
file build_clean/kernel/kernel
# Expected: ELF 64-bit LSB executable, x86-64, version 1 (SYSV), statically linked

# Check multiboot header presence (in linked kernel)
objdump -h build_clean/kernel/kernel | grep -E "\.multiboot|\.text"

# Check entry point
readelf -h build_clean/kernel/kernel | grep "Entry point"
```

## Related Documentation

- [docs/ARCHITECTURAL_OVERVIEW.md](ARCHITECTURAL_OVERVIEW.md) - System architecture
- [kernel/kernel.ld](../kernel/kernel.ld) - Linker script with multiboot section
- [kernel/boot/](../kernel/boot/) - Boot-related source files
