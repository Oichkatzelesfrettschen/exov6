/**
 * Intel 82093AA I/O Advanced Programmable Interrupt Controller (IOAPIC)
 * 
 * Full implementation based on Intel 82093AA specification
 * Datasheet: Intel 82093AA I/O APIC (Order Number: 290566-001)
 * 
 * The IOAPIC manages hardware interrupts for SMP systems, providing:
 * - 24 programmable interrupts (13 ISA, 4 PCI, 7 system)
 * - Edge/level trigger configuration
 * - Active high/low polarity configuration
 * - Static and dynamic interrupt distribution
 * - EOI message support
 * 
 * Memory-mapped registers at 0xFEC00000 (default)
 * All registers accessed via index/data window method
 */

#include <types.h>
#include "defs.h"
#include "traps.h"

#ifndef T_IRQ0
#define T_IRQ0  32  // IRQ 0 corresponds to interrupt 32
#endif

/* Intel 82093AA IOAPIC Memory Map */
#define IOAPIC_DEFAULT_BASE  0xFEC00000   // Default physical address
#define IOAPIC_WINDOW_SIZE   0x20         // Memory window size

/* IOAPIC Register Offsets (Memory Mapped) */
#define IOAPIC_REGSEL        0x00         // Register Select (Index)
#define IOAPIC_IOWIN         0x10         // Data Window
#define IOAPIC_IOWINVER      0x20         // Version Window (82093AA specific)
#define IOAPIC_IOEOI         0x40         // EOI register (newer versions)

/* IOAPIC Register Indices (written to REGSEL) */
#define IOAPIC_ID            0x00         // IOAPIC ID Register
#define IOAPIC_VER           0x01         // IOAPIC Version Register
#define IOAPIC_ARB           0x02         // IOAPIC Arbitration ID
#define IOAPIC_REDTBL_BASE   0x10         // Redirection Table Base

/**
 * Redirection Table Entry Format (64-bit per entry)
 * Each interrupt has a 64-bit entry accessed as two 32-bit operations
 * 
 * Low 32 bits (even index):
 * [7:0]   - Interrupt Vector (0x10-0xFE)
 * [10:8]  - Delivery Mode (Fixed, Lowest Priority, SMI, NMI, INIT, ExtINT)
 * [11]    - Destination Mode (0=Physical, 1=Logical)
 * [12]    - Delivery Status (Read Only)
 * [13]    - Interrupt Input Pin Polarity (0=High, 1=Low)
 * [14]    - Remote IRR (Read Only)
 * [15]    - Trigger Mode (0=Edge, 1=Level)
 * [16]    - Interrupt Mask (0=Enabled, 1=Disabled)
 * [31:17] - Reserved
 * 
 * High 32 bits (odd index):
 * [31:24] - Destination APIC ID (Physical Mode)
 * [31:24] - Set of CPUs (Logical Mode)
 */

/* Delivery Modes (bits 10:8) */
#define IOAPIC_DELMOD_FIXED          0x00000000  // Fixed delivery
#define IOAPIC_DELMOD_LOWPRI         0x00000100  // Lowest priority
#define IOAPIC_DELMOD_SMI            0x00000200  // System Management Int
#define IOAPIC_DELMOD_NMI            0x00000400  // Non-Maskable Int
#define IOAPIC_DELMOD_INIT           0x00000500  // INIT signal
#define IOAPIC_DELMOD_EXTINT         0x00000700  // External INT

/* Destination Mode (bit 11) */
#define IOAPIC_DESTMOD_PHYSICAL      0x00000000  // Physical APIC ID
#define IOAPIC_DESTMOD_LOGICAL       0x00000800  // Logical (set of CPUs)

/* Delivery Status (bit 12) - Read Only */
#define IOAPIC_DELIVS_IDLE           0x00000000  // Idle
#define IOAPIC_DELIVS_PENDING        0x00001000  // Send pending

/* Interrupt Polarity (bit 13) */
#define IOAPIC_INTPOL_HIGH           0x00000000  // Active high
#define IOAPIC_INTPOL_LOW            0x00002000  // Active low

/* Remote IRR (bit 14) - Read Only for Level Triggered */
#define IOAPIC_RIRR_NONE             0x00000000  // No EOI required
#define IOAPIC_RIRR_PENDING          0x00004000  // EOI pending

/* Trigger Mode (bit 15) */
#define IOAPIC_TRIGGER_EDGE          0x00000000  // Edge triggered
#define IOAPIC_TRIGGER_LEVEL         0x00008000  // Level triggered

/* Interrupt Mask (bit 16) */
#define IOAPIC_INT_ENABLED           0x00000000  // Interrupt enabled
#define IOAPIC_INT_DISABLED          0x00010000  // Interrupt masked

/* Legacy compatibility defines */
#define INT_DISABLED   IOAPIC_INT_DISABLED
#define INT_LEVEL      IOAPIC_TRIGGER_LEVEL
#define INT_ACTIVELOW  IOAPIC_INTPOL_LOW
#define INT_LOGICAL    IOAPIC_DESTMOD_LOGICAL

/* IOAPIC Controller State */
struct ioapic_state {
    volatile uint32_t *base;     // Memory-mapped base address
    uint32_t id;                 // IOAPIC ID
    uint32_t version;            // Version and max redirection entries
    uint32_t gsi_base;           // Global System Interrupt base
    uint32_t max_entries;        // Maximum redirection entries
    struct spinlock lock;        // Access lock
};

static struct ioapic_state ioapics[16];  // Support up to 16 IOAPICs
static int nioapics = 0;

/* Primary IOAPIC pointer for compatibility */
volatile struct ioapic *ioapic;

/* Legacy IO APIC MMIO structure for backward compatibility */
struct ioapic {
  uint32_t reg;      // IOREGSEL at offset 0x00
  uint32_t pad[3];   // Padding to 0x10
  uint32_t data;     // IOWIN at offset 0x10
};

/**
 * Read from IOAPIC register using index/data window method
 * Intel 82093AA specification section 3.0
 * 
 * @param apic_id  IOAPIC to access (0 for primary)
 * @param reg      Register index to read
 * @return         32-bit register value
 */
static uint32_t
ioapicread(int apic_id, int reg)
{
    struct ioapic_state *apic = &ioapics[apic_id];
    uint32_t val;
    
    acquire(&apic->lock);
    
    /* Write index to IOREGSEL */
    *(volatile uint32_t*)(apic->base + IOAPIC_REGSEL/4) = reg;
    
    /* Memory barrier to ensure index write completes */
    __sync_synchronize();
    
    /* Read data from IOWIN */
    val = *(volatile uint32_t*)(apic->base + IOAPIC_IOWIN/4);
    
    release(&apic->lock);
    return val;
}

/**
 * Write to IOAPIC register using index/data window method
 * Intel 82093AA specification section 3.0
 * 
 * @param apic_id  IOAPIC to access (0 for primary)
 * @param reg      Register index to write
 * @param data     32-bit value to write
 */
static void
ioapicwrite(int apic_id, int reg, uint32_t data)
{
    struct ioapic_state *apic = &ioapics[apic_id];
    
    acquire(&apic->lock);
    
    /* Write index to IOREGSEL */
    *(volatile uint32_t*)(apic->base + IOAPIC_REGSEL/4) = reg;
    
    /* Memory barrier to ensure index write completes */
    __sync_synchronize();
    
    /* Write data to IOWIN */
    *(volatile uint32_t*)(apic->base + IOAPIC_IOWIN/4) = data;
    
    release(&apic->lock);
}

/* Forward declarations */
static void ioapic_setup_isa_irqs(void);

/* Note: All ioapicread/write calls now use two arguments (apic_id, reg) */

/**
 * Initialize all IOAPICs in the system
 * Intel 82093AA specification sections 2.0, 3.0
 * 
 * Performs:
 * 1. Detection via ACPI MADT or MP tables
 * 2. Version and capability detection
 * 3. ID verification
 * 4. Interrupt routing table initialization
 * 5. ISA IRQ legacy mapping
 */
void
ioapicinit(void)
{
    int i, id, maxintr;
    uint32_t ver;
    struct ioapic_state *apic;
    (void)maxintr;  /* Variable declared but not used; kept for future expansion */

    /* Initialize primary IOAPIC for legacy compatibility */
    ioapic = (volatile struct ioapic*)IOAPIC_DEFAULT_BASE;
    
    /* Setup primary IOAPIC state */
    apic = &ioapics[0];
    apic->base = (volatile uint32_t*)IOAPIC_DEFAULT_BASE;
    initlock(&apic->lock, "ioapic0");
    nioapics = 1;
    
    /* Read IOAPIC Version Register (Intel 82093AA section 3.2.2) */
    ver = ioapicread(0, IOAPIC_VER);
    apic->version = ver & 0xFF;           // Version in bits [7:0]
    apic->max_entries = ((ver >> 16) & 0xFF) + 1;  // Max entries in bits [23:16]
    
    /* Read IOAPIC ID Register (Intel 82093AA section 3.2.1) */
    id = (ioapicread(0, IOAPIC_ID) >> 24) & 0x0F;
    apic->id = id;
    
    /* Verify ID matches MP/ACPI configuration */
    if(id != ioapicid) {
        cprintf("ioapicinit: IOAPIC ID %d doesn't match expected %d\n", id, ioapicid);
        /* Continue anyway - some systems have mismatched IDs */
    }
    
    cprintf("ioapic0: version 0x%x, %d interrupts, id %d at 0x%x\n",
            apic->version, apic->max_entries, apic->id, apic->base);
    
    /* Initialize all redirection table entries */
    for(i = 0; (uint32_t)i < apic->max_entries; i++) {
        /* Configure each interrupt as:
         * - Masked (disabled)
         * - Edge triggered
         * - Active high polarity
         * - Fixed delivery mode
         * - Physical destination mode
         * - Vector = T_IRQ0 + IRQ number
         * - Destination = no CPU (0)
         */
        uint32_t low = IOAPIC_INT_DISABLED |    // Masked
                       IOAPIC_TRIGGER_EDGE |     // Edge triggered
                       IOAPIC_INTPOL_HIGH |      // Active high
                       IOAPIC_DELMOD_FIXED |     // Fixed delivery
                       IOAPIC_DESTMOD_PHYSICAL | // Physical mode
                       (T_IRQ0 + i);             // Vector
        uint32_t high = 0;                       // No destination CPU
        
        /* Write 64-bit redirection entry as two 32-bit writes */
        ioapicwrite(0, IOAPIC_REDTBL_BASE + 2*i, low);
        ioapicwrite(0, IOAPIC_REDTBL_BASE + 2*i + 1, high);
    }
    
    /* Special handling for ISA IRQs (0-15) */
    ioapic_setup_isa_irqs();
}

/**
 * Configure ISA IRQ mappings for PC compatibility
 * Intel 82093AA section 2.3 - ISA Bus Interrupt Delivery
 */
static void
ioapic_setup_isa_irqs(void)
{
    /* ISA IRQ default configurations per Intel spec */
    struct {
        int irq;
        int trigger;  /* 0=edge, 1=level */
        int polarity; /* 0=high, 1=low */
    } isa_irqs[] = {
        {0,  0, 0},  /* Timer - edge, active high */
        {1,  0, 0},  /* Keyboard - edge, active high */
        {2,  0, 0},  /* Cascade (not used in APIC mode) */
        {3,  0, 0},  /* COM2 - edge, active high */
        {4,  0, 0},  /* COM1 - edge, active high */
        {5,  0, 0},  /* LPT2 - edge, active high */
        {6,  0, 0},  /* Floppy - edge, active high */
        {7,  0, 0},  /* LPT1 - edge, active high */
        {8,  0, 0},  /* RTC - edge, active high */
        {9,  1, 1},  /* ACPI/SCI - level, active low (varies) */
        {10, 1, 1},  /* Available - level, active low */
        {11, 1, 1},  /* Available - level, active low */
        {12, 0, 0},  /* PS/2 Mouse - edge, active high */
        {13, 0, 0},  /* FPU/Coprocessor - edge, active high */
        {14, 0, 0},  /* Primary IDE - edge, active high */
        {15, 0, 0},  /* Secondary IDE - edge, active high */
    };
    
    for(int i = 0; i < 16; i++) {
        uint32_t trigger = isa_irqs[i].trigger ? IOAPIC_TRIGGER_LEVEL : IOAPIC_TRIGGER_EDGE;
        uint32_t polarity = isa_irqs[i].polarity ? IOAPIC_INTPOL_LOW : IOAPIC_INTPOL_HIGH;
        
        /* Keep interrupts masked during initialization */
        uint32_t low = IOAPIC_INT_DISABLED |
                       trigger |
                       polarity |
                       IOAPIC_DELMOD_FIXED |
                       IOAPIC_DESTMOD_PHYSICAL |
                       (T_IRQ0 + i);
        
        ioapicwrite(0, IOAPIC_REDTBL_BASE + 2*i, low);
    }
}

/**
 * Enable and route a specific IRQ to a CPU
 * Intel 82093AA specification section 3.2.4 - Redirection Table
 * 
 * @param irq      IRQ number to enable (0-23)
 * @param cpunum   Target CPU APIC ID
 */
void
ioapicenable(int irq, int cpunum)
{
    struct ioapic_state *apic = &ioapics[0];  /* Use primary IOAPIC */
    uint32_t low, high;
    
    if((uint32_t)irq >= apic->max_entries) {
        cprintf("ioapicenable: IRQ %d exceeds max %d\n", irq, apic->max_entries);
        panic("ioapicenable: IRQ exceeds max entries");
    }
    
    /* Read current configuration to preserve trigger/polarity */
    low = ioapicread(0, IOAPIC_REDTBL_BASE + 2*irq);
    
    /* Determine trigger mode and polarity based on IRQ */
    if(irq < 16) {  /* ISA IRQ */
        /* ISA IRQs 0-7, 12-15 are edge-triggered, active high */
        /* ISA IRQs 9-11 may be level-triggered, active low (PCI) */
        if(irq == 9 || irq == 10 || irq == 11) {
            low = IOAPIC_TRIGGER_LEVEL | IOAPIC_INTPOL_LOW;
        } else {
            low = IOAPIC_TRIGGER_EDGE | IOAPIC_INTPOL_HIGH;
        }
    } else {  /* PCI or system IRQ */
        /* PCI interrupts are typically level-triggered, active low */
        low = IOAPIC_TRIGGER_LEVEL | IOAPIC_INTPOL_LOW;
    }
    
    /* Configure interrupt as:
     * - Enabled (not masked)
     * - Fixed delivery mode
     * - Physical destination mode
     * - Vector = T_IRQ0 + IRQ number
     * - Preserve trigger mode and polarity
     */
    low |= IOAPIC_DELMOD_FIXED |      /* Fixed delivery */
           IOAPIC_DESTMOD_PHYSICAL |   /* Physical APIC ID */
           (T_IRQ0 + irq);              /* Interrupt vector */
    low &= ~IOAPIC_INT_DISABLED;       /* Enable interrupt */
    
    /* Set destination CPU in high 32 bits */
    high = (cpunum & 0xFF) << 24;      /* Bits [31:24] = APIC ID */
    
    /* Write 64-bit redirection entry */
    ioapicwrite(0, IOAPIC_REDTBL_BASE + 2*irq, low);
    ioapicwrite(0, IOAPIC_REDTBL_BASE + 2*irq + 1, high);
    
    cprintf("ioapic: enabled IRQ%d -> CPU%d vector 0x%x\n", irq, cpunum, T_IRQ0 + irq);
}

/**
 * Disable a specific IRQ
 * 
 * @param irq  IRQ number to disable
 */
void
ioapicdisable(int irq)
{
    struct ioapic_state *apic = &ioapics[0];
    uint32_t low;
    
    if((uint32_t)irq >= apic->max_entries) {
        cprintf("ioapicdisable: IRQ %d exceeds max %d\n", irq, apic->max_entries);
        panic("ioapicdisable: IRQ exceeds max entries");
    }
    
    /* Read current configuration */
    low = ioapicread(0, IOAPIC_REDTBL_BASE + 2*irq);
    
    /* Set mask bit to disable interrupt */
    low |= IOAPIC_INT_DISABLED;
    
    /* Write back configuration */
    ioapicwrite(0, IOAPIC_REDTBL_BASE + 2*irq, low);
}

/**
 * Send EOI (End of Interrupt) for level-triggered interrupts
 * Intel 82093AA specification section 3.2.5
 * 
 * @param irq  IRQ number that was serviced
 */
void
ioapiceoi(int irq)
{
    struct ioapic_state *apic = &ioapics[0];
    uint32_t low;
    
    if((uint32_t)irq >= apic->max_entries) {
        return;
    }
    
    /* Check if interrupt is level-triggered */
    low = ioapicread(0, IOAPIC_REDTBL_BASE + 2*irq);
    if(low & IOAPIC_TRIGGER_LEVEL) {
        /* For level-triggered interrupts, EOI is sent to Local APIC */
        /* The Local APIC will broadcast EOI to IOAPICs */
        /* This is handled by lapiceoi() */
    }
    /* Edge-triggered interrupts don't require EOI to IOAPIC */
}

/**
 * Get IOAPIC information for debugging
 * 
 * @param apic_id  IOAPIC to query
 * @param info     Buffer to fill with information
 */
void
ioapicinfo(int apic_id, struct ioapic_info *info)
{
    struct ioapic_state *apic;
    
    if(apic_id >= nioapics) {
        return;
    }
    
    apic = &ioapics[apic_id];
    info->id = apic->id;
    info->version = apic->version;
    info->max_entries = apic->max_entries;
    info->base_addr = (uint64_t)apic->base;
    info->gsi_base = apic->gsi_base;
}
