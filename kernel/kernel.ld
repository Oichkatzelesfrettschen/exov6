/* Linker script for ExoKernel v6 x86_64 with Multiboot2 Boot Support */

OUTPUT_FORMAT("elf64-x86-64", "elf64-x86-64", "elf64-x86-64")
OUTPUT_ARCH(i386:x86-64)
ENTRY(multiboot2_entry)

/* Memory layout constants */
BOOT_PHYS_BASE = 0x100000;           /* Physical load address (1MB) */
KERNEL_VIRT_BASE = 0xFFFFFFFF80000000; /* High-half virtual base (-2GB) */
KERNEL_PHYS_OFFSET = 0x100000;       /* Physical offset from VIRT_BASE */

SECTIONS
{
  /* =========================================================================
   * BOOT SECTIONS - Identity mapped (VMA = LMA = physical address)
   * These must be addressable by 32-bit code before paging is enabled
   * ========================================================================= */

  . = BOOT_PHYS_BASE;

  /* PVH ELF note - required for QEMU x86_64 -kernel boot */
  .note.Xen : {
    KEEP(*(.note.Xen))
  }

  /* Multiboot2 header - must be in first 32KB of file */
  .boot : {
    PROVIDE(__boot_start = .);
    *(.multiboot)
    . = ALIGN(16);
  }

  /* 32-bit boot code - runs before paging enabled */
  .boot_text : {
    *(.boot_text)
    . = ALIGN(16);
  }

  /* Boot data - GDT, pointers, etc. */
  .boot_data : {
    *(.boot_data)
    . = ALIGN(4096);
  }

  /* Boot BSS - page tables, stack (not loaded, zeroed) */
  .boot_bss (NOLOAD) : {
    PROVIDE(__boot_bss_start = .);
    *(.boot_bss)
    . = ALIGN(4096);
    PROVIDE(__boot_bss_end = .);
  }

  PROVIDE(__boot_end = .);
  __boot_size = __boot_end - __boot_start;

  /* =========================================================================
   * KERNEL SECTIONS - High-half virtual addresses
   * VMA at KERNEL_VIRT_BASE + offset, LMA continues from boot sections
   * ========================================================================= */

  /* Calculate where kernel virtual addresses start */
  . = KERNEL_VIRT_BASE + KERNEL_PHYS_OFFSET + __boot_size;
  __kernel_virt_start = .;

  /* Kernel text - code segment */
  .text : AT(__boot_end) {
    PROVIDE(__text_start = .);
    *(.text .stub .text.* .gnu.linkonce.t.*)
    . = ALIGN(0x1000);
    PROVIDE(etext = .);
  }

  /* Read-only data */
  .rodata : {
    *(.rodata .rodata.* .gnu.linkonce.r.*)
  }

  /* Ensure proper alignment for data section */
  . = ALIGN(0x1000);

  /* Read-write data (initialized) */
  .data : {
    PROVIDE(__data_start = .);
    *(.data .data.* .gnu.linkonce.d.*)
    PROVIDE(edata = .);
  }

  /* Uninitialized data (BSS) */
  .bss : {
    PROVIDE(__bss_start = .);
    *(.dynbss)
    *(.bss .bss.* .gnu.linkonce.b.*)
    *(COMMON)
    . = ALIGN(0x1000);
    PROVIDE(__bss_end = .);
    PROVIDE(end = .);
  }

  /* =========================================================================
   * DEBUG SECTIONS
   * ========================================================================= */

  /* Debugging sections */
  .stab 0 : { *(.stab) }
  .stabstr 0 : { *(.stabstr) }
  .stab.excl 0 : { *(.stab.excl) }
  .stab.exclstr 0 : { *(.stab.exclstr) }
  .stab.index 0 : { *(.stab.index) }
  .stab.indexstr 0 : { *(.stab.indexstr) }
  .comment 0 : { *(.comment) }

  /* DWARF debug sections */
  .debug          0 : { *(.debug) }
  .line           0 : { *(.line) }
  .debug_srcinfo  0 : { *(.debug_srcinfo) }
  .debug_sfnames  0 : { *(.debug_sfnames) }
  .debug_aranges  0 : { *(.debug_aranges) }
  .debug_pubnames 0 : { *(.debug_pubnames) }
  .debug_info     0 : { *(.debug_info .gnu.linkonce.wi.*) }
  .debug_abbrev   0 : { *(.debug_abbrev) }
  .debug_line     0 : { *(.debug_line) }
  .debug_frame    0 : { *(.debug_frame) }
  .debug_str      0 : { *(.debug_str) }
  .debug_loc      0 : { *(.debug_loc) }
  .debug_macinfo  0 : { *(.debug_macinfo) }
  .debug_weaknames 0 : { *(.debug_weaknames) }
  .debug_funcnames 0 : { *(.debug_funcnames) }
  .debug_typenames 0 : { *(.debug_typenames) }
  .debug_varnames  0 : { *(.debug_varnames) }
  .debug_pubtypes 0 : { *(.debug_pubtypes) }
  .debug_ranges   0 : { *(.debug_ranges) }
  .gnu.attributes 0 : { KEEP (*(.gnu.attributes)) }

  /DISCARD/ : { *(.note.GNU-stack) *(.gnu_debuglink) *(.gnu.lto_*) }
}
