// Boot loader.
//
// Part of the boot block, along with bootasm.S, which calls bootmain().
// bootasm.S has put the processor into protected 32-bit mode.
// bootmain() loads an ELF kernel image from the disk starting at
// sector 1 and then jumps to the kernel entry routine.

#include "types.h"
#include "elf.h"
#include "x86.h"
#include "memlayout.h"
#include <stdint.h>

#define SECTSIZE  512

void readseg(uint8_t*, uint32_t, uint32_t);

void
bootmain(uint32_t kaslr_physical_offset) // Renamed parameter
{
  struct elfhdr *elf;
  // struct proghdr *ph, *eph; // Original
  void (*entry)(void);
  // uint8_t* pa; // Original, replaced by segment_actual_physical_load_addr

  uintptr_t actual_kernel_physical_base = (uintptr_t)EXTMEM + kaslr_physical_offset; // New calculation

  elf = (struct elfhdr*)0x10000;  // scratch space

  // Read 1st page off disk
  readseg((uint8_t*)elf, 4096, 0);

  // Is this an ELF executable?
  if(elf->magic != ELF_MAGIC)
    return;  // let bootasm.S handle error

  // Load each program segment (ignores ph flags).
  // ph = (struct proghdr*)((uint8_t*)elf + elf->phoff); // Original
  // eph = ph + elf->phnum; // Original
  // for(; ph < eph; ph++){ // Original
  //   pa = (uint8_t*)(uintptr_t)ph->paddr; // Original
  //   readseg(pa, ph->filesz, ph->off); // Original
  //   if(ph->memsz > ph->filesz) // Original
  //     stosb(pa + ph->filesz, 0, ph->memsz - ph->filesz); // Original
  // } // Original

  struct proghdr *ph_elf_offset, *eph_elf_offset;
  ph_elf_offset = (struct proghdr*)((uint8_t*)elf + elf->phoff); // ph_elf_offset is based on physical elf pointer
  eph_elf_offset = ph_elf_offset + elf->phnum;

  for(; ph_elf_offset < eph_elf_offset; ph_elf_offset++){
    // ph_elf_offset->paddr is the LINK address of the segment.
    // KERNLINK is the LINK address of the kernel base.
    // actual_kernel_physical_base is the new randomized PHYSICAL address where kernel base is loaded.
    uintptr_t segment_link_virtual_address = (uintptr_t)ph_elf_offset->paddr;
    uintptr_t segment_offset_from_kernlink = segment_link_virtual_address - (uintptr_t)KERNLINK; // KERNLINK comes from memlayout.h
    uintptr_t segment_actual_physical_load_addr = actual_kernel_physical_base + segment_offset_from_kernlink;

    readseg((uint8_t*)segment_actual_physical_load_addr, ph_elf_offset->filesz, ph_elf_offset->off);
    if(ph_elf_offset->memsz > ph_elf_offset->filesz)
      stosb((uint8_t*)segment_actual_physical_load_addr + ph_elf_offset->filesz, 0, ph_elf_offset->memsz - ph_elf_offset->filesz);
  }

  // Call the entry point from the ELF header.
  // This is the fixed VIRTUAL address (e.g., KERNLINK + offset).
  // The page tables set up in bootasm64.S are responsible for mapping this
  // virtual address to the randomized physical memory.
  void (*kernel_virtual_entry)(void);
  kernel_virtual_entry = (void(*)(void))(uintptr_t)elf->entry; // elf->entry is KERNLINK-based
  kernel_virtual_entry();
}

void
waitdisk(void)
{
  // Wait for disk ready.
  while((inb(0x1F7) & 0xC0) != 0x40)
    ;
}

// Read a single sector at offset into dst.
void
readsect(void *dst, uint32_t offset)
{
  // Issue command.
  waitdisk();
  outb(0x1F2, 1);   // count = 1
  outb(0x1F3, offset);
  outb(0x1F4, offset >> 8);
  outb(0x1F5, offset >> 16);
  outb(0x1F6, (offset >> 24) | 0xE0);
  outb(0x1F7, 0x20);  // cmd 0x20 - read sectors

  // Read data.
  waitdisk();
  insl(0x1F0, dst, SECTSIZE/4);
}

// Read 'count' bytes at 'offset' from kernel into physical address 'pa'.
// Might copy more than asked.
void
readseg(uint8_t* pa, uint32_t count, uint32_t offset)
{
  uint8_t* epa;

  epa = pa + count;

  // Round down to sector boundary.
  pa -= offset % SECTSIZE;

  // Translate from bytes to sectors; kernel starts at sector 1.
  offset = (offset / SECTSIZE) + 1;

  // If this is too slow, we could read lots of sectors at a time.
  // We'd write more to memory than asked, but it doesn't matter --
  // we load in increasing order.
  for(; pa < epa; pa += SECTSIZE, offset++)
    readsect(pa, offset);
}
