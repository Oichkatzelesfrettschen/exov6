# QEMU Boot Status

## Current State (January 2025)

The FeuerBird kernel builds successfully as a 64-bit ELF executable with full
multiboot2 and PVH boot support. Boot infrastructure verified but QEMU direct
boot requires GRUB2.

### Boot Infrastructure Status

| Component | Status | Notes |
|-----------|--------|-------|
| Multiboot2 header | COMPLETE | In .boot section at 0x100000 |
| PVH ELF note | COMPLETE | XEN_ELFNOTE_PHYS32_ENTRY for QEMU |
| 32-to-64-bit trampoline | COMPLETE | Page tables, GDT, long mode |
| High-half kernel mapping | COMPLETE | 0xFFFFFFFF80000000+ |
| Serial boot diagnostics | COMPLETE | MTPL sequence on COM1 |

### Binary Layout (Verified)

```
Section Layout:
  .note.Xen    @ 0x100000 (PVH entry note)
  .boot        @ 0x100010 (Multiboot2 header)
  .boot_text   @ 0x100610 (32-bit entry code)
  .boot_data   @ 0x100700 (GDT, pointers)
  .boot_bss    @ 0x101000 (Page tables, stack) [NOLOAD]
  .text        @ 0xFFFFFFFF80109000 (Kernel code)
  .rodata      @ 0xFFFFFFFF8010E000 (Read-only data)
  .data        @ 0xFFFFFFFF80110000 (Initialized data)
  .bss         @ 0xFFFFFFFF80110020 (Uninitialized data)

Entry point: 0x100610 (multiboot2_entry)
```

### QEMU Boot Limitations

QEMU's x86_64 `-kernel` flag does NOT support Multiboot2 directly:

- **x86_64 -kernel**: Expects Linux boot protocol or PVH (PVH note added but
  requires specific CPU state setup that QEMU's loader doesn't provide)
- **i386 -kernel**: Supports Multiboot1, but requires 32-bit ELF

### Boot Method: GRUB2 ISO (Recommended)

```bash
# Install GRUB if not present
sudo pacman -S grub xorriso

# Create ISO directory structure
mkdir -p iso/boot/grub
cp build/kernel/kernel iso/boot/

# Create GRUB config
cat > iso/boot/grub/grub.cfg << 'EOF'
set timeout=0
set default=0

menuentry "FeuerBird Exokernel" {
    multiboot2 /boot/kernel
    boot
}
EOF

# Create bootable ISO
grub-mkrescue -o feuerbird.iso iso/

# Boot with QEMU
qemu-system-x86_64 -cdrom feuerbird.iso -serial stdio -no-reboot
```

### Expected Serial Output

When booting successfully, the kernel outputs diagnostic characters on COM1:

```
MTPL
```

Where:
- `M` = Multiboot entry reached
- `T` = Page tables set up
- `P` = About to enable paging
- `L` = Long mode entered

### Alternative Boot Methods

#### Method 1: Direct ELF Loading (Development Only)

```bash
# Uses QEMU loader device - loads ELF but CPU starts in real mode
qemu-system-x86_64 \
    -device loader,file=build/kernel/kernel,cpu-num=0 \
    -nographic -serial mon:stdio
```

Note: This loads the kernel into memory but does NOT transfer control to the
entry point. CPU starts at BIOS reset vector.

#### Method 2: QEMU with Multiboot (32-bit)

Not applicable - kernel is 64-bit ELF.

### Verification Commands

```bash
# Check ELF format
file build/kernel/kernel
# Expected: ELF 64-bit LSB executable, x86-64

# Check multiboot header presence
objdump -h build/kernel/kernel | grep -E "\.boot|\.note"

# Check entry point
readelf -h build/kernel/kernel | grep "Entry point"
# Expected: Entry point address: 0x100610

# Check PVH note
readelf -n build/kernel/kernel
# Should show: Xen note with XEN_ELFNOTE_PHYS32_ENTRY (0x12)

# Check sections are at correct addresses
objdump -h build/kernel/kernel | head -20
```

### Technical Details

#### Memory Mapping

The boot trampoline sets up dual page table mappings:

1. **Identity mapping**: PML4[0] -> PDPT -> PD (first 1GB)
   - Physical 0x00000000-0x3FFFFFFF maps to virtual 0x00000000-0x3FFFFFFF

2. **High-half mapping**: PML4[511] -> PDPT_high[510] -> PD
   - Physical 0x00000000-0x3FFFFFFF maps to virtual 0xFFFFFFFF80000000+

This allows the kernel to run at high virtual addresses while boot code
executes at low physical addresses.

#### Boot Sequence

1. Bootloader (GRUB) loads kernel at 0x100000 physical
2. Transfers control to `multiboot2_entry` in 32-bit protected mode
3. Boot code sets up page tables with identity + high-half mapping
4. Enables PAE, loads PML4 into CR3
5. Enables long mode via EFER MSR
6. Enables paging (activates long mode)
7. Far jump to `long_mode_entry` in 64-bit mode
8. Sets up segments, stack
9. Jumps to `main64` at high-half address

### Related Documentation

- [ARCHITECTURAL_OVERVIEW.md](ARCHITECTURAL_OVERVIEW.md) - System architecture
- [kernel/kernel.ld](../kernel/kernel.ld) - Linker script
- [src/arch/x64/multiboot2.S](../src/arch/x64/multiboot2.S) - Boot trampoline
