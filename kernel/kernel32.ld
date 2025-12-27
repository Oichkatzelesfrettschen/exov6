/* Linker script for FeuerBird Exokernel i686 (32-bit) */

OUTPUT_FORMAT("elf32-i386", "elf32-i386", "elf32-i386")
OUTPUT_ARCH(i386)
ENTRY(_start)

SECTIONS
{
  /* Kernel is loaded at 1MB physical, linked at 0x80100000 virtual */
  . = 0x80100000;

  /* Multiboot header must be in first 8KB */
  .text : AT(0x100000) {
    *(.multiboot)
    *(.text .stub .text.* .gnu.linkonce.t.*)
    . = ALIGN(0x1000);
    PROVIDE(etext = .);
  }

  /* Read-only data */
  .rodata : {
    *(.rodata .rodata.* .gnu.linkonce.r.*)
  }

  /* Ensure page alignment for data */
  . = ALIGN(0x1000);

  /* Read-write data (initialized) */
  .data : {
    *(.data .data.* .gnu.linkonce.d.*)
    PROVIDE(edata = .);
  }

  /* Uninitialized data (BSS) */
  .bss : {
    *(.dynbss)
    *(.bss .bss.* .gnu.linkonce.b.*)
    *(COMMON)
    . = ALIGN(0x1000);
    PROVIDE(end = .);
  }

  /* Debug sections */
  .stab 0 : { *(.stab) }
  .stabstr 0 : { *(.stabstr) }
  .stab.excl 0 : { *(.stab.excl) }
  .stab.exclstr 0 : { *(.stab.exclstr) }
  .stab.index 0 : { *(.stab.index) }
  .stab.indexstr 0 : { *(.stab.indexstr) }
  .comment 0 : { *(.comment) }

  /* DWARF debug sections */
  .debug 0 : { *(.debug) }
  .line 0 : { *(.line) }
  .debug_srcinfo 0 : { *(.debug_srcinfo) }
  .debug_sfnames 0 : { *(.debug_sfnames) }
  .debug_aranges 0 : { *(.debug_aranges) }
  .debug_pubnames 0 : { *(.debug_pubnames) }
  .debug_info 0 : { *(.debug_info .gnu.linkonce.wi.*) }
  .debug_abbrev 0 : { *(.debug_abbrev) }
  .debug_line 0 : { *(.debug_line) }
  .debug_frame 0 : { *(.debug_frame) }
  .debug_str 0 : { *(.debug_str) }
  .debug_loc 0 : { *(.debug_loc) }
  .debug_macinfo 0 : { *(.debug_macinfo) }

  /DISCARD/ : { *(.eh_frame) *(.comment) }
}
