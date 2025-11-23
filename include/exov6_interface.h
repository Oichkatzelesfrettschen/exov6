// include/exov6_interface.h

#ifndef EXOV6_INTERFACE_H
#define EXOV6_INTERFACE_H

#ifdef __KERNEL__
#include <types.h>
#else
#include <stdint.h>
#endif

// --- Kernel Constants ---
#define EXO_MAX_ENV     64      // Max environments (processes)
#define EXO_PAGE_SIZE   4096    // Fixed page size

// --- Lattice Security Labels (Placeholder for Phase 2) ---
typedef uint32_t label_t;
#define LABEL_LOW       0x0
#define LABEL_HIGH      0x1

// --- System Call Numbers ---
// We replace the standard xv6 syscall numbers with these primitives.

// 1. Environment (Process) Control
#define SYS_env_create  1   // Create a new, blank environment (no memory yet)
#define SYS_env_run     2   // Yield CPU to a specific env (Scheduler Activation)
#define SYS_env_destroy 3   // Kill an environment

// 2. Memory Management (The Heart of Exokernel)
#define SYS_page_alloc  4   // Allocate a physical page
#define SYS_page_map    5   // Map a physical page to a virtual addr in an Env
#define SYS_page_unmap  6   // Unmap a page
#define SYS_page_stat   7   // Query status/owner of a physical page

// 3. IPC & Lattice Control
#define SYS_ipc_send    8   // Send a small message (register passing) to Env
#define SYS_ipc_recv    9   // Blocking receive
#define SYS_set_label   10  // (Privileged) Set the security label of a resource

// 4. Hardware IO (Capabilities)
#define SYS_disk_io     11  // Read/Write raw block (checked against capability)

// 5. Debug/Bootstrap (Temporary)
#define SYS_cputs       12  // Print string to console (for bootstrapping)

// 6. Exception/Upcall Handling
#define SYS_env_set_handler 13  // Set the upcall entry point and exception stack
#define SYS_env_resume      14  // Return from upcall, restore saved context

// --- Trap Cause Codes (x86_64) ---
#define EXO_TRAP_DIVIDE       0   // Divide error
#define EXO_TRAP_DEBUG        1   // Debug exception
#define EXO_TRAP_NMI          2   // Non-maskable interrupt
#define EXO_TRAP_BRKPT        3   // Breakpoint
#define EXO_TRAP_OFLOW        4   // Overflow
#define EXO_TRAP_BOUND        5   // Bound range exceeded
#define EXO_TRAP_ILLOP        6   // Invalid opcode
#define EXO_TRAP_DEVICE       7   // Device not available
#define EXO_TRAP_DBLFLT       8   // Double fault
#define EXO_TRAP_TSS         10   // Invalid TSS
#define EXO_TRAP_SEGNP       11   // Segment not present
#define EXO_TRAP_STACK       12   // Stack fault
#define EXO_TRAP_GPFLT       13   // General protection fault
#define EXO_TRAP_PGFLT       14   // Page fault
#define EXO_TRAP_FPERR       16   // Floating point error
#define EXO_TRAP_ALIGN       17   // Alignment check
#define EXO_TRAP_MCHK        18   // Machine check
#define EXO_TRAP_SIMDERR     19   // SIMD floating point error

// IRQ base (x86_64)
#define EXO_IRQ_BASE         32
#define EXO_IRQ_TIMER        (EXO_IRQ_BASE + 0)
#define EXO_IRQ_KBD          (EXO_IRQ_BASE + 1)
#define EXO_IRQ_COM1         (EXO_IRQ_BASE + 4)

// --- The Trap Frame Contract (x86_64) ---
// When we upcall into the LibOS, we push this struct onto the user exception
// stack so the LibOS knows why it woke up and can restore state afterward.
// This matches the kernel trapframe layout for easy copying.
struct ExoTrapFrame {
    // Metadata about the trap
    uint64_t trapno;        // Trap number (cause)
    uint64_t err;           // Error code (for page faults: contains flags)
    uint64_t addr;          // Faulting address (CR2 for page faults)

    // Saved program state
    uint64_t rip;           // Instruction pointer at time of fault
    uint64_t rflags;        // CPU flags
    uint64_t rsp;           // Stack pointer (original, before exception)

    // General purpose registers
    uint64_t rax, rbx, rcx, rdx;
    uint64_t rsi, rdi, rbp;
    uint64_t r8, r9, r10, r11, r12, r13, r14, r15;

    // Segment registers (usually not needed but included for completeness)
    uint64_t cs, ss, ds, es, fs, gs;
};

// --- MMIO Constants ---
#define PHYSTOP         0x88000000ULL   // End of RAM (QEMU virt default)
#define UART0_BASE      0x10000000ULL   // QEMU virt UART0

// --- VirtIO MMIO (Phase 7: User-Space Block Driver) ---
#define VIRTIO0_BASE    0x10001000ULL   // QEMU virt VirtIO Block Device
#define VIRTIO0_IRQ     1               // External IRQ for VirtIO0

// VirtIO MMIO Register Offsets (from VirtIO 1.0 spec)
#define VIRTIO_MMIO_MAGIC_VALUE         0x000   // Must be 0x74726976 ("virt")
#define VIRTIO_MMIO_VERSION             0x004   // Device version (1 = legacy, 2 = modern)
#define VIRTIO_MMIO_DEVICE_ID           0x008   // Subsystem device ID (2 = block)
#define VIRTIO_MMIO_VENDOR_ID           0x00C   // Vendor ID
#define VIRTIO_MMIO_DEVICE_FEATURES     0x010   // Device feature bits
#define VIRTIO_MMIO_DRIVER_FEATURES     0x020   // Driver feature bits
#define VIRTIO_MMIO_GUEST_PAGE_SIZE     0x028   // Guest page size (legacy)
#define VIRTIO_MMIO_QUEUE_SEL           0x030   // Queue selector
#define VIRTIO_MMIO_QUEUE_NUM_MAX       0x034   // Max queue size
#define VIRTIO_MMIO_QUEUE_NUM           0x038   // Queue size
#define VIRTIO_MMIO_QUEUE_ALIGN         0x03C   // Alignment (legacy)
#define VIRTIO_MMIO_QUEUE_PFN           0x040   // Queue PFN (legacy)
#define VIRTIO_MMIO_QUEUE_READY         0x044   // Queue ready
#define VIRTIO_MMIO_QUEUE_NOTIFY        0x050   // Queue notify
#define VIRTIO_MMIO_INTERRUPT_STATUS    0x060   // Interrupt status
#define VIRTIO_MMIO_INTERRUPT_ACK       0x064   // Interrupt acknowledge
#define VIRTIO_MMIO_STATUS              0x070   // Device status

// VirtIO Device Status bits
#define VIRTIO_STATUS_ACKNOWLEDGE       0x01
#define VIRTIO_STATUS_DRIVER            0x02
#define VIRTIO_STATUS_FEATURES_OK       0x08
#define VIRTIO_STATUS_DRIVER_OK         0x04
#define VIRTIO_STATUS_FAILED            0x80

// VirtIO Block Device Features
#define VIRTIO_BLK_F_SIZE_MAX           (1 << 1)
#define VIRTIO_BLK_F_SEG_MAX            (1 << 2)
#define VIRTIO_BLK_F_GEOMETRY           (1 << 4)
#define VIRTIO_BLK_F_RO                 (1 << 5)
#define VIRTIO_BLK_F_BLK_SIZE           (1 << 6)

// VirtIO Magic Value ("virt" in little-endian ASCII)
#define VIRTIO_MAGIC                    0x74726976

#endif // EXOV6_INTERFACE_H
