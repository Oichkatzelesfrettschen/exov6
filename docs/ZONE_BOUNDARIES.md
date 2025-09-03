# Zone Boundary Documentation

## Zone Separation Model

### x86-64 Virtual Memory Layout (Long Mode)

```
0xFFFFFFFFFFFFFFFF ┌─────────────────────┐ Canonical high half
                   │   Kernel Zone       │ (PML4[511:256])
                   │   (Ring 0 pages)    │ SMEP/SMAP protected
KERNBASE           ├─────────────────────┤ 0xFFFF800000000000
0xFFFF7FFFFFFFFFFF │   Non-canonical     │ 
                   │      (causes #GP)   │
0x0000800000000000 ├─────────────────────┤
0x00007FFFFFFFFFFF │   LibOS Zone        │ Canonical low half
                   │   (Ring 3 + privs)  │ (PML4[255:1])
0x0000000040000000 ├─────────────────────┤
                   │  Application Zone   │ 
                   │    (Ring 3 only)    │ User pages
0x0000000000400000 ├─────────────────────┤
                   │   Low Reserved      │
0x0000000000000000 └─────────────────────┘
```

### Hardware Isolation Mechanisms

#### Paging-Based Protection
- **Page Table Permissions**: User/Supervisor (U/S), Read/Write (R/W), Execute Disable (XD)
- **SMEP** (Supervisor Mode Execution Prevention): Ring 0 cannot execute Ring 3 pages
- **SMAP** (Supervisor Mode Access Prevention): Ring 0 cannot access Ring 3 data without AC=1
- **PCID** (Process Context Identifier): TLB tagging to avoid flushes on context switch

## Zone Transition Points

### Safe Entry Points

1. **Kernel → LibOS**
   - Via registered callbacks
   - Capability-authenticated
   - State preserved

2. **LibOS → Application**
   - Through POSIX interfaces
   - Signal delivery
   - Shared memory segments

3. **Application → LibOS**
   - System call emulation
   - Library function calls
   - IPC channels

## Boundary Enforcement

### Hardware-Level Protection

```c
// x86-64 Page Table Entry flags (Intel SDM Vol. 3, Section 4.5)
#define PTE_PRESENT    0x001  // Page present
#define PTE_WRITE      0x002  // Writable
#define PTE_USER       0x004  // User accessible
#define PTE_PWT        0x008  // Page Write Through
#define PTE_PCD        0x010  // Page Cache Disable
#define PTE_ACCESSED   0x020  // Accessed
#define PTE_DIRTY      0x040  // Dirty
#define PTE_PS         0x080  // Page Size (2MB/1GB)
#define PTE_GLOBAL     0x100  // Global
#define PTE_NX      0x8000000000000000ULL  // No Execute

// Zone-specific page permissions
#define KERN_PAGE_FLAGS  (PTE_PRESENT | PTE_WRITE)                    // Ring 0 only
#define LIBOS_PAGE_FLAGS (PTE_PRESENT | PTE_WRITE | PTE_USER)         // Ring 3 privileged
#define APP_PAGE_FLAGS   (PTE_PRESENT | PTE_USER)                     // Ring 3 read-only
#define NOEXEC_FLAGS     (PTE_NX)                                     // Data pages
```

### CPU Security Features

```c
// Enable SMEP/SMAP in CR4 (Intel SDM Vol. 3, Section 4.6)
#define CR4_SMEP  0x00100000  // Bit 20: SMEP Enable
#define CR4_SMAP  0x00200000  // Bit 21: SMAP Enable
#define CR4_PCIDE 0x00020000  // Bit 17: PCID Enable

static inline void enable_cpu_security_features(void) {
    uint64_t cr4 = read_cr4();
    cr4 |= CR4_SMEP | CR4_SMAP | CR4_PCIDE;
    write_cr4(cr4);
}
```

### Control Flow Integrity (CET)

```c
// Intel CET Shadow Stack (if supported) - Intel SDM Vol. 1, Section 18
#define CET_SHSTK_EN   0x01  // Enable shadow stack
#define CET_WRSS_EN    0x02  // Enable WRSS instruction
#define CET_ENDBR_EN   0x04  // Enable ENDBR instruction

// MSR addresses for CET
#define MSR_IA32_S_CET          0x6A2
#define MSR_IA32_PL3_SSP        0x6A7
```

## Capability Requirements

### Cross-Zone Operations

| Operation | Source | Target | Required Capability |
|-----------|--------|--------|-------------------|
| Read | App | LibOS | CAP_TYPE_IPC |
| Write | App | LibOS | CAP_TYPE_IPC + WRITE |
| Execute | LibOS | Kernel | CAP_TYPE_ZONE |
| Map | App | App | CAP_TYPE_MEMORY |

### Capability Validation

```c
// Every cross-zone access validated
if (!cap_validate(cap, ZONE_TRANSITION)) {
    zone_fault_handler(ZONE_VIOLATION);
}
```

## Security Boundaries

### Information Flow Control

```
Application ← LibOS ← Kernel
     ↓         ↓        ↓
   [CAP]     [CAP]    [HW]
```

- Downward flow requires capabilities
- Upward flow through defined interfaces
- No lateral flow without mediation

### Isolation Guarantees

1. **Memory Isolation**
   - No shared pages by default
   - Capability-mediated sharing
   - Revocable mappings

2. **Execution Isolation**
   - Separate stacks per zone
   - Control transfer validation
   - Return address protection

3. **State Isolation**
   - Zone-local register sets
   - Cleared on transition
   - Saved/restored atomically

## Violation Handling

#### Hardware Exception Vectors

```c
// x86-64 Exception vectors (Intel SDM Vol. 3, Section 6.3)
#define VEC_PAGE_FAULT    14   // #PF: Page fault
#define VEC_GENERAL_PROTECTION 13  // #GP: General protection fault
#define VEC_STACK_FAULT   12   // #SS: Stack segment fault
#define VEC_INVALID_TSS   10   // #TS: Invalid TSS

// Exception handlers
extern void page_fault_handler(struct trapframe *tf);
extern void general_protection_handler(struct trapframe *tf);
```

#### SMEP/SMAP Violation Detection

```c
// Page fault error code bits (Intel SDM Vol. 3, Section 4.7)
#define PF_PRESENT    0x01  // Page was present
#define PF_WRITE      0x02  // Write access
#define PF_USER       0x04  // User mode access
#define PF_RSVD       0x08  // Reserved bit violation
#define PF_INSTR      0x10  // Instruction fetch
#define PF_PK         0x20  // Protection key violation
#define PF_SS         0x40  // Shadow stack violation

void page_fault_handler(struct trapframe *tf) {
    uint64_t cr2 = read_cr2();  // Faulting address
    uint32_t error = tf->err;   // Error code
    
    if (error & PF_USER) {
        // User mode fault - check zone boundaries
        zone_boundary_violation(cr2, error);
    } else {
        // Kernel mode fault - SMEP/SMAP violation?
        if (error & PF_INSTR) {
            panic("SMEP violation: kernel executed user page at %p", cr2);
        }
        if (!(error & PF_PRESENT)) {
            panic("SMAP violation: kernel accessed user page at %p", cr2);
        }
    }
}
```

### Response Actions

1. **Log violation**
2. **Terminate violator**
3. **Revoke capabilities**
4. **Alert administrator**

## TLB Management

#### PCID-Aware Context Switching

```c
// Process Context Identifier support (Intel SDM Vol. 3, Section 4.10.1)
#define PCID_KERNEL   0x000  // Kernel PCID
#define PCID_LIBOS    0x001  // LibOS PCID  
#define PCID_APP_BASE 0x100  // Application PCIDs start here

// INVPCID instruction types (Intel SDM Vol. 2B, INVPCID)
#define INVPCID_TYPE_INDIVIDUAL  0  // Individual page
#define INVPCID_TYPE_SINGLE_CTXT 1  // Single context
#define INVPCID_TYPE_ALL_CTXT    2  // All contexts
#define INVPCID_TYPE_ALL_NON_GLOBAL 3  // All non-global

void context_switch_pcid(uint16_t pcid, uint64_t cr3) {
    // Load new CR3 with PCID (bits 11:0)
    uint64_t new_cr3 = (cr3 & ~0xFFFULL) | pcid;
    write_cr3(new_cr3);
}
```

#### TLB Shootdown Protocol

```c
// IPI-based TLB invalidation
void tlb_shootdown_range(void *start, void *end, uint16_t pcid) {
    struct tlb_shootdown_data data = {
        .start_addr = (uint64_t)start,
        .end_addr = (uint64_t)end,
        .pcid = pcid
    };
    
    // Send IPI to all other CPUs
    send_ipi_all_but_self(TLB_SHOOTDOWN_VECTOR, &data);
    
    // Invalidate local TLB
    invlpg_range(start, end);
}
```

## Performance Considerations

### Fast Path Optimizations

```c
// Cached zone checks
if (likely(current_zone == target_zone)) {
    return ZONE_CHECK_OK;  // Same zone, no check
}
```

### Batched Transitions

```c
// Amortize transition cost
zone_batch_transition(transitions, count);
```

## Testing Zone Boundaries

#### Hardware Feature Tests
```c
// test/cpu_features_test.c - Verify SMEP/SMAP/CET support
void test_smep_violation(void);
void test_smap_violation(void);
void test_cet_shadow_stack(void);
```

#### Isolation Tests  
```c
// test/zone_isolation_test.c - Zone boundary enforcement
void test_kernel_user_isolation(void);
void test_pcid_context_separation(void);
void test_nx_bit_enforcement(void);
```

#### Performance Tests
```c
// test/tlb_performance_test.c - TLB/PCID efficiency
void benchmark_context_switch_latency(void);
void benchmark_tlb_shootdown_overhead(void);
```