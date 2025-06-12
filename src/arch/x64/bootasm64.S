#
# src/arch/x64/bootasm64.S - x86-64 Bootloader Assembly Code
#
# This file contains the initial assembly code responsible for bootstrapping the system
# from 16-bit real mode through 32-bit protected mode, and finally into 64-bit long mode.
# Key responsibilities include:
#   - Initializing segment registers.
#   - Enabling the A20 line.
#   - Setting up Global Descriptor Tables (GDTs) for protected and long modes.
#   - Configuring Control Registers (CR0, CR3, CR4) for mode transitions and paging.
#   - Enabling Long Mode via the EFER MSR.
#   - Setting up minimal page tables for initial identity mapping.
#   - Attempting to generate a random physical offset for Kernel Address Space
#     Layout Randomization (KASLR) using RDRAND.
#   - Calling the C language entry point (`bootmain`).
#
# The macros SEG_ASM, SEG_ASM64, ENABLE_A20, SETUP_PROT_MODE, INIT_PROT_MODE_DATA
# are assumed to be defined in "asm_common.h".
# Constants for memory layout and MMU are from "memlayout.h" and "mmu.h".
#

#include "asm.h"
#include "memlayout.h"
#include "mmu.h"
#include "../asm_common.h"

# Processor Feature and Control Defines
#define CR4_PAE 0x00000020              # Physical Address Extension (CR4 bit 5)
#define KASLR_ENTROPY_MASK 0x7FE00000   # Mask for KASLR physical offset:
                                        #  - Applies to a 32-bit random value.
                                        #  - Zeroes bits 0-20: Ensures 2MB alignment (offset is multiple of 2MB).
                                        #  - Zeroes bits 31-29: Ensures offset is less than 0x80000000 (2GB).
                                        #  - Effective entropy range for offset: [0, 2GB - 2MB] in 2MB steps.
#define RDRAND_SUPPORTED_BIT (1 << 30)  # CPUID.(EAX=01H, ECX=0):ECX[bit 30] indicates RDRAND support.
#define CPUID_LEAF_FEATURES 1           # CPUID EAX=01H for querying standard processor features.

# Page Table Entry (PTE) Flags (subset, common ones)
.equ PTE_P, (1 << 0)    # Present
.equ PTE_W, (1 << 1)    # Read/Write
.equ PTE_U, (1 << 2)    # User/Supervisor
.equ PTE_PS, (1 << 7)   # Page Size (0 for 4KB page, 1 for 2MB/1GB page)

# Common PTE Flag combinations
.equ PTE_P_W_FLAGS, (PTE_P | PTE_W)          # Present, Read/Write
.equ PTE_P_W_PS_FLAGS, (PTE_P | PTE_W | PTE_PS) # Present, Read/Write, 2MB Page

# Kernel Memory Layout Constants (ensure these match C definitions if any)
.equ KERNLINK, 0x80100000 # Default link address for the kernel
.equ EXTMEM, 0x100000     # Start of extended memory, physical base for kernel loading

#
# Initial 16-bit Real Mode Setup
#
# This section contains the code that executes when the processor starts in
# 16-bit real mode. Its primary goal is to transition the processor to 32-bit
# protected mode.
#
.code16                # Assemble for 16-bit mode
.globl start
start:
    # Disable interrupts.
    # Interrupts must be disabled during the mode switch and GDT setup to prevent
    # unexpected behavior from handlers that are not yet set up for protected mode.
    cli

    # Zero out segment registers (DS, ES, SS).
    # In real mode, segment registers hold the upper 16 bits of the segment base address.
    # Setting them to zero ensures a known, flat memory model (0x00000-0xFFFFF) initially.
    xorw %ax,%ax
    movw %ax,%ds        # Data Segment
    movw %ax,%es        # Extra Segment
    movw %ax,%ss        # Stack Segment

    # Enable A20 line.
    # The A20 line (21st address line) needs to be enabled to access memory
    # above 1MB. Historically, it was gated for compatibility with older software
    # that relied on address wrapping at 1MB.
    # ENABLE_A20 is a macro defined in asm_common.h, typically handling
    # communication with the keyboard controller or system chipset to enable A20.
    ENABLE_A20

    # Load the Global Descriptor Table (GDT) for 32-bit protected mode
    # and jump to 32-bit code.
    # SETUP_PROT_MODE is a macro (defined in asm_common.h) that:
    # 1. Loads the GDT register (GDTR) with the address and limit of gdt32
    #    (passed as 'gdtdesc32').
    # 2. Enables protected mode by setting the PE bit in CR0.
    # 3. Performs a far jump to the 32-bit code segment.
    # Parameters:
    #   gdtdesc32: The descriptor for the 32-bit GDT.
    #   1<<3:      The selector for the 32-bit code segment.
    #              Index 1 (001) in GDT, RPL 0 (00), TI 0 (GDT) -> 00001000b = 0x08.
    #              The '<<3' converts GDT index to selector format.
    #   prot32:    The label of the 32-bit code to jump to.
    SETUP_PROT_MODE(gdtdesc32, 1<<3, prot32)

#
# 32-bit Protected Mode Setup
#
# This section executes after the processor has transitioned to 32-bit protected mode.
#
.code32                # Assemble for 32-bit mode
prot32:
    # Initialize data segment registers for 32-bit protected mode.
    INIT_PROT_MODE_DATA(2<<3) # Uses selector 0x10 (Kernel Data Segment from gdt32)

    # KASLR Offset Generation (moved from longmode to prot32, before CR3 load)
    # This logic must run before CR3 is loaded if the page tables themselves
    # (or the logic writing to them) rely on %esi containing the offset,
    # or if %esi is needed by bootmain which is called from longmode after paging.
    # For this implementation, we populate a PDE dynamically using %esi.
    #
    # Initialize KASLR physical offset to 0 (default: no offset).
    # %esi will carry this offset to bootmain AND be used for PDE calculation.
    movl $0, %esi

    # Check for RDRAND instruction support via CPUID.
    movl $CPUID_LEAF_FEATURES, %eax
    cpuid
    testl $RDRAND_SUPPORTED_BIT, %ecx
    jz rdrand_failed_or_unsupported_kaslr

    # RDRAND is supported; attempt to get a 32-bit random number.
    rdrand %eax
    jnc rdrand_failed_or_unsupported_kaslr # If CF=0, RDRAND failed.

    # RDRAND succeeded. Apply mask.
    andl $KASLR_ENTROPY_MASK, %eax
    movl %eax, %esi

rdrand_failed_or_unsupported_kaslr:
    # %esi now holds the KASLR physical offset (or 0).

    # --- Dynamically Populate Page Directory Entry (PDE) for KERNLINK ---
    # This section calculates the physical address of the kernel based on EXTMEM and
    # the KASLR offset, then creates a 2MB page table entry (PDE) to map KERNLINK's
    # virtual address (0x80100000, within the 2GB-3GB VA range covered by kernel_pd_table)
    # to this randomized physical address.

    # KERNLINK (0x80100000) is at VA 2GB + 0x100000.
    # This VA falls into the range covered by pdpt_table[2], which points to kernel_pd_table.
    # The specific entry within kernel_pd_table is index 0, because:
    #   (KERNLINK_VA - VA_base_of_kernel_pd_table) / 2MB_page_size
    # = (0x80100000 - 0x80000000) / 0x200000 = 0x100000 / 0x200000 = 0.
    # So, kernel_pd_table[0] maps VA [0x80000000, 0x80000000 + 2MB - 1].

    pushl   %eax                    # Save EAX, as it's used extensively.
    pushl   %ebx                    # Save EBX (just in case, though not directly used here).
    pushl   %edi                    # Save EDI, as it's used to construct the PDE.

    # Calculate the target physical address for the kernel's base.
    movl    %esi, %eax              # EAX = kaslr_physical_offset.
    addl    $EXTMEM, %eax           # EAX = EXTMEM (e.g. 0x100000) + kaslr_physical_offset.
                                    # This is the actual randomized physical base of the kernel.
                                    # Both EXTMEM and kaslr_physical_offset are assumed/ensured
                                    # to be 2MB aligned, so their sum is also 2MB aligned.
                                    # This address will be the base address field in the PDE.
    movl    %eax, %edi              # EDI = Physical base for the kernel's 2MB page.

    # Combine the physical base with page flags for a 2MB page.
    # PTE_P_W_PS_FLAGS = Present (PTE_P), Read/Write (PTE_W), PageSize (PTE_PS for 2MB).
    orl     $PTE_P_W_PS_FLAGS, %edi # EDI now holds the complete lower 32 bits of the PDE value.
                                    # e.g., (Physical Base for Kernel) | PTE_P | PTE_W | PTE_PS.

    # Write the calculated PDE into the first entry of kernel_pd_table.
    # kernel_pd_table is the page directory responsible for the VA range starting at 2GB.
    # kernel_pd_table[0] maps the VA range [2GB, 2GB + 2MB - 1].
    # Since KERNLINK (0x80100000) is typically 2GB + a small offset (like 1MB),
    # it falls within this first 2MB page mapped by kernel_pd_table[0].
    movl    %edi, kernel_pd_table     # Store lower 32 bits of PDE into kernel_pd_table[0].
    movl    $0, kernel_pd_table + 4   # Store upper 32 bits of PDE. Since physical addresses for these
                                    # 2MB pages are expected to be < 4GB, the upper 32 bits are 0.

    # --- Store a copy of the KERNLINK PDE for debugging/verification ---
    # %edi still holds the lower 32-bits of the PDE: (EXTMEM + kaslr_offset) | PTE_P_W_PS_FLAGS
    # The upper 32-bits are 0.
    # This location kaslr_debug_kernlink_pde must be identity mapped.
    # It is within the first 2MB, so boot_pd_table[0] covers it.
    movl    %edi, kaslr_debug_kernlink_pde
    movl    $0, kaslr_debug_kernlink_pde + 4
    # --- End of KERNLINK PDE debug store ---

    popl    %edi                    # Restore EDI.
    popl    %ebx                    # Restore EBX.
    popl    %eax                    # Restore EAX.
    # --- PDE for KERNLINK's initial 2MB page is now populated in kernel_pd_table[0] ---

    # --- Setup for Long Mode Transition ---
    # The order of operations is critical:
    # 1. Load GDT for 64-bit mode (gdtdesc64).
    # 2. Enable PAE in CR4 (Physical Address Extension). Also other CR4 bits like SMEP/SMAP.
    # 3. Set LME bit in EFER MSR (Long Mode Enable).
    # 4. Load CR3 with the physical address of PML4 table (pml4_table).
    # 5. Enable paging (PG bit in CR0). Also set WP (Write Protect).
    # After this, the CPU is in paged protected mode, ready for the long jump.

    # 1. Load GDT for 64-bit mode.
    #    GDT is in low memory, identity mapped by the new page tables.
    lgdt    gdtdesc64

    # 2. Configure CR4: Enable PAE for long mode, plus security features.
    movl    %cr4, %eax
    orl     $(CR4_PAE | CR4_SMEP | CR4_SMAP | CR4_UMIP), %eax
    movl    %eax, %cr4

    # 3. Enable Long Mode (LME bit in EFER MSR).
    movl    $0xC0000080, %ecx  # IA32_EFER MSR address
    rdmsr                     # Read EFER into EDX:EAX
    orl     $(1<<8), %eax     # Set LME bit (EFER.LME, bit 8)
    wrmsr                     # Write back to EFER

    # 4. Load CR3 with the physical address of the new PML4 table (pml4_table).
    #    This makes the new page table hierarchy known to the CPU. It becomes active
    #    once paging is enabled in CR0.
    movl    $pml4_table, %eax
    movl    %eax, %cr3

    # 5. Enable Paging (PG bit in CR0) and Write Protect (WP bit).
    #    CR0_PE (Protection Enable) is already set from the initial jump to protected mode.
    movl    %cr0, %eax
    orl     $(CR0_PG | CR0_WP), %eax # Set PG and WP bits.
    movl    %eax, %cr0        # Paging is NOW active! All subsequent memory accesses are via virtual addresses.

    # Transition to Long Mode (64-bit code).
    # A long jump (ljmp) is used to load a 64-bit code segment selector and
    # jump to the 64-bit entry point.
    # Parameter 1: Selector for the 64-bit kernel code segment.
    #              This must match an entry in gdt64. Index 1 in gdt64 is the
    #              64-bit code segment (STA_X|STA_R with L-bit), so selector is 1<<3 = 0x08.
    #              Original was (3<<3) = 0x18, which pointed to an undefined GDT entry.
    # Parameter 2: $longmode. This is the virtual address of the 64-bit code
    #              entry point. Paging must be active to resolve this address.
    ljmp $(1<<3), $longmode # Corrected selector to 0x08 (index 1 in gdt64)

#
# 64-bit Long Mode Execution
#
# This section contains the code that executes after the processor has successfully
# transitioned to 64-bit long mode.
# %esi (from prot32) contains the KASLR physical offset for bootmain.
#
.code64                # Assemble for 64-bit mode
longmode:
    # %esi already contains the KASLR physical offset from the .code32 section.
    # No further KASLR offset generation needed here.

    # Set up the initial stack pointer for 64-bit mode.
    # The choice of '$start' (physical address 0, start of bootloader code) as RSP
    # is unconventional for a general-purpose stack, as it implies the stack grows
    # downwards into the bootloader's own code and data if not managed carefully.
    # This setup is often found in minimal bootloaders where stack usage before
    # transitioning to a proper kernel stack is extremely limited.
    # A more robust setup would allocate a dedicated stack area.
    mov $start,%rsp

    # Call the 64-bit C entry point (bootmain).
    # - %esi: Contains the KASLR physical offset (0 if RDRAND failed or unsupported).
    # - CS: Set to 0x08 (Kernel Code Segment from gdt64 via the long jump).
    # - SS: Implicitly 0x10 (Kernel Data Segment from gdt64) if segment registers are set up accordingly in longmode,
    #       or 0 if no explicit setup is done (which is unsafe). Typically, after a long jump,
    #       data segment registers (DS, ES, SS) are loaded with a valid data segment selector.
    #       (This minimal bootloader does not show explicit DS/ES/SS setup post long jump before bootmain).
    # bootmain is a C function defined in kernel/bootmain.c.
    call bootmain

    # Infinite loop if bootmain returns (which it should not).
    # This prevents execution from falling through into undefined memory.
    # The label '1:' is a common, concise way to denote a local, unnamed loop.
1:  jmp 1b

#
# Global Descriptor Tables (GDTs)
#
# GDTs define the system's memory segments, their access rights, and properties.
# Each GDT entry (descriptor) is 8 bytes long.
# A segment selector, used to load into a segment register, is formed as:
#   Bits 15-3: GDT Index (the entry number in the GDT)
#   Bit  2   : Table Indicator (0 = GDT, 1 = LDT)
#   Bits 1-0 : Requested Privilege Level (RPL)
# For kernel segments, RPL is usually 0. So, selector = (GDT Index << 3).
#

# GDT for 32-bit Protected Mode
.p2align 2             # Align GDT base to a 4-byte boundary (2^2 bytes = 4 bytes) for performance.
gdt32:
    # Null Descriptor (Index 0)
    # Base=0, Limit=0. This descriptor is required by the architecture and cannot be used to access memory.
    # SEG_NULLASM is a macro (likely ` .quad 0 ` or ` .long 0,0 `) defined in "asm.h".
    SEG_NULLASM

    # Kernel Code Segment (Index 1, Selector 0x08)
    # Base Address = 0x00000000. Limit = 0xFFFFFFFF (covers 4GB address space).
    # The SEG_ASM macro (defined in "asm.h") constructs the 8-byte descriptor.
    # Parameters: (type, base, limit)
    #   type: STA_X (Executable), STA_R (Readable) -> Defines an Execute/Read code segment.
    # Expected flags set by SEG_ASM for a 32-bit code segment:
    #   P (Present) = 1            (Segment is valid)
    #   DPL (Descriptor Privilege Level) = 0 (Kernel mode)
    #   S (Descriptor Type) = 1      (Code or Data segment, not a system segment)
    #   Type field: Execute/Read flags.
    #   G (Granularity) = 1          (Limit is in 4KB units, so 0xFFFFF * 4KB = 4GB)
    #   D/B (Default operand size) = 1 (32-bit segment)
    #   L (Long mode code flag) = 0    (Not a 64-bit code segment)
    #   AVL (Available for s/w use) = 0
    SEG_ASM(STA_X|STA_R, 0, 0xffffffff) # Selector: (1 << 3) | 0 = 0x08

    # Kernel Data Segment (Index 2, Selector 0x10)
    # Base Address = 0x00000000. Limit = 0xFFFFFFFF (covers 4GB address space).
    #   type: STA_W (Writable) -> Defines a Read/Write data segment.
    # Expected flags set by SEG_ASM for a 32-bit data segment:
    #   P=1, DPL=0, S=1, Type for Read/Write, G=1, D/B=1.
    SEG_ASM(STA_W, 0, 0xffffffff)       # Selector: (2 << 3) | 0 = 0x10

# GDT Descriptor for 32-bit mode (gdtdesc32)
# This 6-byte structure is loaded into the GDTR register using the LGDT instruction.
# It specifies the size (limit) and the linear base address of the gdt32.
gdtdesc32:
    .word (gdtdesc32 - gdt32 - 1) # Limit: Size of (gdt32) in bytes, minus 1.
    .long gdt32                   # Base Address: Linear address where gdt32 starts.

# GDT for 64-bit Long Mode
# This GDT is used once the processor transitions to long mode.
# It defines segments appropriate for 64-bit operation.
.p2align 2             # Align GDT base to a 4-byte boundary for performance.
gdt64:
    # Null Descriptor (Index 0) - Still required.
    SEG_NULLASM

    # Kernel Code Segment (64-bit) (Index 1, Selector 0x08)
    # Base Address and Limit are effectively ignored (treated as 0) for code/data segments in 64-bit flat model.
    # The SEG_ASM64 macro (defined in "asm.h") constructs the 8-byte descriptor.
    # Parameters: (type, base, limit)
    #   type: STA_X (Executable), STA_R (Readable)
    # Expected flags set by SEG_ASM64 for a 64-bit code segment:
    #   P=1, DPL=0, S=1, Type for Execute/Read.
    #   L (Long mode code flag) = 1 (Crucial: signifies a 64-bit code segment).
    #   D/B (Default operand size) = 0 (Must be 0 when L=1).
    #   G=1 (Granularity, though limit is ignored, usually set for consistency).
    # This segment is used by the `ljmp $(1<<3), $longmode` instruction.
    SEG_ASM64(STA_X|STA_R,0,0) # Selector: (1 << 3) | 0 = 0x08

    # Kernel Data Segment (64-bit) (Index 2, Selector 0x10)
    # Base and Limit are ignored.
    #   type: STA_W (Writable)
    # Expected flags set by SEG_ASM64 for a 64-bit data segment:
    #   P=1, DPL=0, S=1, Type for Read/Write.
    #   L=0 (Not a code segment). D/B is irrelevant for 64-bit data segments.
    # This segment would be used if DS, ES, SS are explicitly set to 0x10 after entering long mode.
    SEG_ASM64(STA_W,0,0)       # Selector: (2 << 3) | 0 = 0x10

# GDT Descriptor for 64-bit mode (gdtdesc64)
# This structure is loaded into the GDTR for long mode.
# The GDTR in 64-bit mode supports a 64-bit base address.
# The LGDT instruction when executed in 32-bit mode (as it is here, before the final ljmp)
# typically loads a 16-bit limit and a 32-bit base address if a 32-bit operand size is used.
# The structure below is 8 bytes:
#   - 2 bytes for the limit.
#   - 4 bytes for the lower 32 bits of the base address.
#   - 4 bytes for the upper 32 bits of the base address (though `lgdt` in 32-bit context might only use the lower part).
# For the GDT to be addressable above 4GB, `lgdt` would need to be executed in 64-bit mode or use a 64-bit operand size.
# Given that `gdt64` is in low memory (addressable by 32 bits), this setup is functional.
gdtdesc64:
    .word (gdtdesc64 - gdt64 - 1) # Limit: Size of (gdt64) in bytes, minus 1.
    .long gdt64                   # Base Address (lower 32 bits): Linear address of gdt64.
    .long 0                       # Base Address (upper 32 bits): Assumed 0, as gdt64 is in low memory.

#
# Page Table Structures for Long Mode
#
# These tables are structured for 4-level paging (PML4, PDPT, PD, PT).
# For simplicity and to cover necessary ranges for boot and KASLR:
# - The first 2MB of physical memory is identity-mapped (VA=PA).
# - The kernel, linked at KERNLINK (e.g., 0x80100000), is mapped to its
#   KASLR-randomized physical address (EXTMEM + kaslr_offset) using a 2MB page.
#
# All tables must be 4KB aligned as required by the x86-64 architecture.
#

.p2align 12 # Align to 4KB page boundary.
kernel_pd_table:   # Page Directory for the KERNLINK Virtual Address (VA) range.
                   # This PD maps the 1GB VA range [2GB, 3GB-1], covered by pdpt_table[2].
                   # Each entry in this PD maps a 2MB page.
    # Entry 0 of this PD will be dynamically populated. It maps the VA range
    # [2GB, 2GB + 2MB - 1] to the physical address [EXTMEM + kaslr_offset, EXTMEM + kaslr_offset + 2MB - 1].
    # Since KERNLINK (e.g., 0x80100000 = 2GB + 0x100000) falls within this first 2MB VA slice
    # of the 2GB-3GB range, this entry effectively maps the kernel's starting virtual address.
    .zero 8 * 512  # Initialize all 512 Page Directory Entries (PDEs) to zero. Each PDE is 8 bytes.
                   # Total size: 512 * 8 bytes = 4KB.

.p2align 12 # Align to 4KB page boundary.
boot_pd_table:     # Page Directory for the bootloader's low VA range.
                   # This PD maps the 1GB VA range [0GB, 1GB-1], covered by pdpt_table[0].
                   # Each entry in this PD maps a 2MB page.
    # PDE[0]: Identity maps the first 2MB of physical memory.
    #   VA range: [0x00000000, 0x001FFFFF] (first 2MB)
    #   PA range: [0x00000000, 0x001FFFFF] (first 2MB)
    #   Physical Base Address for PDE: 0x0.
    #   Flags: PTE_P_W_PS_FLAGS (Present, Read/Write, PageSize for 2MB page).
    .quad 0x0 | PTE_P_W_PS_FLAGS
    .zero 8 * 511  # Other 511 PDEs are zero, meaning no further mappings in this 1GB VA range.

.p2align 12 # Align to 4KB page boundary.
pdpt_table:        # Page Directory Pointer Table.
                   # Each entry maps a 1GB region of VA space.
                   # This PDPT is pointed to by pml4_table[0].
    # PDPT Entry 0 (PDPTE[0]): Maps VA range [0GB, 1GB-1].
    #   Points to: boot_pd_table.
    #   Flags: PTE_P_W_FLAGS (Present, Read/Write). The PS bit is 0 here, as it points to a PD.
    .quad boot_pd_table + PTE_P_W_FLAGS

    # PDPT Entry 1 (PDPTE[1]): Maps VA range [1GB, 2GB-1].
    #   Currently unused and zeroed.
    .zero 8 * 1

    # PDPT Entry 2 (PDPTE[2]): Maps VA range [2GB, 3GB-1].
    #   This range includes KERNLINK (e.g., 0x80100000).
    #   Points to: kernel_pd_table.
    #   Flags: PTE_P_W_FLAGS (Present, Read/Write).
    .quad kernel_pd_table + PTE_P_W_FLAGS

    # Remaining (512 - 3 = 509) PDPTEs are zero.
    .zero 8 * (512-3)

.p2align 12 # Align to 4KB page boundary.
pml4_table:        # Page Map Level 4 Table (Top-level paging structure).
                   # Each entry maps a 512GB region of VA space.
    # PML4 Entry 0 (PML4E[0]): Maps VA range [0GB, 512GB-1].
    #   Points to: pdpt_table.
    #   Flags: PTE_P_W_FLAGS (Present, Read/Write).
    .quad pdpt_table + PTE_P_W_FLAGS

    # Other 511 PML4Es are zero, meaning VA ranges beyond the first 512GB are not mapped.
    .zero 8 * 511

#
# Debugging Data Area
#
# This section can be used to store intermediate values from the bootloader
# for later inspection by a debugger if needed.
# Ensure any addresses here are identity mapped by the boot page tables.
#
.p2align 3 # Align to 8 bytes for .quad
kaslr_debug_kernlink_pde:
    # This location will store the 64-bit Page Directory Entry (PDE) that maps
    # the KERNLINK virtual address (specifically, the 2MB page containing KERNLINK's start)
    # to its KASLR-randomized physical address.
    # Format: [ Physical Base Address (2MB aligned) | Flags (PTE_P_W_PS) ]
    # Stored by the dynamic PDE population logic in .code32 section.
    .quad 0
