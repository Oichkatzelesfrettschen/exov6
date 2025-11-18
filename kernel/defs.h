#pragma once

/* Kernel build marker - prevents userspace API conflicts */
#ifndef EXO_KERNEL
#define EXO_KERNEL 1
#endif

#include <stdint.h>
#include <stddef.h>
#include "kernel_compat.h"

#include "types.h"
#include "param.h"
#include <compiler_attrs.h>

#if __has_include("config.h")
# include "config.h"
#endif

/* Use modern lock subsystem - prevents spinlock.h from declaring conflicting qspin_* */
#define __EXOLOCK_H_INCLUDED

#include "spinlock.h"
#include "proc.h"
#include "ipc.h"
#include "cap.h"
#include "service.h"
#include "exo_cpu.h"
#include "exo_disk.h"
#include "exo_ipc.h"
#include "fastipc.h"

#ifdef __x86_64__
# include "trapframe.h"
  typedef struct context64 context_t;
#elif defined(__aarch64__)
# include "trapframe.h"
  typedef struct context64 context_t;
#else
  typedef struct context context_t;
#endif

#define EXO_CONTEXT_T

struct buf;
struct context;
struct file;
struct inode;
struct pipe;
struct proc;
struct spinlock;
struct sleeplock;
struct stat;
struct superblock;
struct exo_cap;
struct exo_blockcap;
struct exo_sched_ops;
struct dag_node;
struct exo_stream;
struct endpoint;
struct rtcdate;

// process table and scheduler lock defined in proc.c
extern struct ptable ptable;
extern struct spinlock sched_lock;

// bio.c
void binit(void);
struct buf *bread(uint32_t dev, uint32_t blockno);
void brelse(struct buf *);
void bwrite(struct buf *);  /* Write buffer to disk */

// console.c
void consoleinit(void);
void cprintf(const char *, ...);
void consoleintr(int (*)(void));
_Noreturn void panic(const char *);

// exec.c
int exec(const char *path, char *const argv[]);

// file.c
struct file *filealloc(void);
void fileclose(struct file *);
struct file *filedup(struct file *);
void fileinit(void);
int fileread(struct file *, char *, size_t);
int filestat(struct file *, struct stat *);
int filewrite(struct file *, const char *, size_t);

// fs.c
void readsb(int dev, struct superblock *sb);
int dirlink(struct inode *, const char *name, uint32_t inum);
struct inode *dirlookup(struct inode *, const char *name, uint32_t *);
struct inode *ialloc(uint32_t dev, short type);
struct inode *idup(struct inode *);
void iinit(int dev);
void ilock(struct inode *);
void iput(struct inode *);
void iunlock(struct inode *);
void iunlockput(struct inode *);
void iupdate(struct inode *);
int namecmp(const char *, const char *);
struct inode *namei(const char *);
struct inode *nameiparent(const char *, char *);
int readi(struct inode *, char *, uint32_t offset, size_t);
void stati(struct inode *, struct stat *);
int writei(struct inode *, const char *, uint32_t offset, size_t);

// ide.c
void ideinit(void);
void ideintr(void);
void iderw(struct buf *);

// ioapic.c
void ioapicenable(int irq, int cpu);
extern uint8_t ioapicid;
void ioapicinit(void);
struct ioapic_info {
    uint32_t id;
    uint32_t version;
    uint32_t max_entries;
    uint64_t base_addr;
    uint32_t gsi_base;
};
void ioapicinfo(int apic_id, struct ioapic_info *info);

// kalloc.c
char *kalloc(void);
void kfree(char *);
void kinit1(void *vstart, void *vend);
void kinit2(void *vstart, void *vend);

// kbd.c
void kbdintr(void);

// lapic.c
void cmostime(struct rtcdate *r);
int lapicid(void);
extern volatile uint32_t *lapic;
void lapiceoi(void);
void lapicinit(void);
void lapicstartap(uint8_t apicid, uint32_t pciptr);
void microdelay(int us);

// log.c
void initlog(int dev);
void log_write(struct buf *);
void begin_op(void);
void end_op(void);

// mp.c
extern int ismp;
void mpinit(void);

// picirq.c
void picenable(int irq);
void picinit(void);

// pipe.c
EXO_NODISCARD int pipealloc(struct file **readp, struct file **writep);
void pipeclose(struct pipe *, int);
int piperead(struct pipe *, struct file *, char *, size_t);
int pipewrite(struct pipe *, struct file *, const char *, size_t);

// proc.c
void cpuid(uint32_t leaf, uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d);
_Noreturn void exit(int status);
int fork(void);
int growproc(int);
int kill(int);
int sigsend(int pid, int sig);
struct cpu *mycpu(void);
struct proc *myproc(void);
void pinit(void);
void procdump(void);
_Noreturn void scheduler(void);
void sched(void);
void setproc(struct proc *);
void sleep(void *chan, struct spinlock *);
void ksleep(void *chan, struct spinlock *);  /* Kernel sleep (atomically release lock and sleep) */
void userinit(void);
int wait(void);
void wakeup(void *chan);
void yield(void);
struct proc *pctr_lookup(uint32_t);
struct proc *allocproc(void);

// swtch.S
void swtch(context_t **old, context_t *new);

// spinlock.c
void acquire(struct spinlock *);
void getcallerpcs(void *v, uint32_t pcs[]);
int holding(struct spinlock *);
void initlock(struct spinlock *, const char *name);
void release(struct spinlock *);
void pushcli(void);
void popcli(void);
/* Modern qspinlock functions moved to exo_lock.h
 * Use: #include "exo_lock.h" and struct qspinlock (not struct spinlock!)
 *
 * Legacy compatibility wrappers (deprecated):
 */
#ifdef USE_LEGACY_SPINLOCK_API
void qspin_lock(struct spinlock *);
void qspin_unlock(struct spinlock *);
int qspin_trylock(struct spinlock *);
#endif

// sleeplock.c
void acquiresleep(struct sleeplock *);
void releasesleep(struct sleeplock *);
int holdingsleep(struct sleeplock *);
void initsleeplock(struct sleeplock *, const char *name);

// string.c
char *safestrcpy(char *dst, const char *src, size_t n);

// syscall.c
int argint(int n, int *ip);
int argptr(int n, char **pp, size_t size);
int argstr(int n, char **pp);
int fetchint(uintptr_t addr, int *ip);
int fetchstr(uintptr_t addr, char **pp);
void syscall(void);

// timer.c
void timerinit(void);

// trap.c
void idtinit(void);
extern uint32_t ticks;
void tvinit(void);
extern struct qspinlock tickslock;
void exo_pctr_transfer(struct trapframe *tf);

// uart.c
void uartinit(void);
void uartintr(void);
void uartputc(int);

// vm.c
void seginit(void);
void kvmalloc(void);
pde_t *setupkvm(void);
#ifdef __x86_64__
pml4e_t *setupkvm64(void);
#endif
char *uva2ka(pde_t *, char *);
int allocuvm(pde_t *, uint32_t oldsz, uint32_t newsz);
int deallocuvm(pde_t *, uint32_t oldsz, uint32_t newsz);
void freevm(pde_t *);
void inituvm(pde_t *, const char *init, uint32_t sz);
int loaduvm(pde_t *, const char *src, struct inode *, uint32_t off, uint32_t sz);
pde_t *copyuvm(pde_t *, uint32_t sz);
void switchuvm(struct proc *);
void switchkvm(void);
#ifdef __x86_64__
int copyout(pde_t *, uint64_t va, const void *p, uint32_t len);
#else
int copyout(pde_t *, uint32_t va, const void *p, uint32_t len);
#endif
void clearpteu(pde_t *pgdir, char *uva);
#ifdef __x86_64__
int insert_pte(pde_t *, void *va, uint64_t perm, int flags);
#else
int insert_pte(pde_t *, void *va, uint32_t perm, int flags);
#endif

// Exokernel extensions (detailed declarations in include/exo.h)
// Note: kernel code should use include/exo.h, NOT include/exokernel.h
exo_cap exo_alloc_irq(uint32_t irq, uint32_t rights);
int exo_irq_wait(exo_cap cap, uint32_t *irqp);
int exo_irq_ack(exo_cap cap);
int irq_trigger(uint32_t irq);
exo_cap exo_alloc_ioport(uint32_t port);
exo_cap exo_bind_irq(uint32_t irq);
exo_cap exo_alloc_dma(uint32_t chan);
exo_cap exo_alloc_hypervisor(void);
int hv_launch_guest(exo_cap cap, const char *path);

void cap_table_init(void);
cap_id_t cap_table_alloc(uint16_t type, uint32_t resource, uint32_t rights, uint32_t owner);
int cap_table_lookup(cap_id_t id, struct cap_entry *out);
void cap_table_inc(cap_id_t id);
void cap_table_dec(cap_id_t id);
int cap_table_remove(cap_id_t id);

// Service management
int service_register(const char *name, const char *path, service_options_t opts);
int service_add_dependency(const char *name, const char *dependency);
void service_notify_exit(struct proc *p);

// Streams and schedulers
void exo_stream_register(struct exo_stream *);
void exo_stream_halt(void);
void exo_stream_yield(void);
void dag_sched_init(void);
void beatty_sched_init(void);
struct exo_sched_ops *dag_sched_ops(void);
struct exo_sched_ops *beatty_sched_ops(void);
void beatty_dag_stream_init(void);
void beatty_sched_set_tasks(exo_cap a, exo_cap b);
void streams_sched_init(void);
void streams_stop(void);
void streams_yield(void);
void fastipc_send(zipc_msg_t *);
int sys_ipc_fast(void);
int sys_ipc(void);
void endpoint_send(struct endpoint *, zipc_msg_t *);
int endpoint_recv(struct endpoint *, zipc_msg_t *);
void dag_node_init(struct dag_node *, exo_cap);
void dag_node_set_priority(struct dag_node *, int);
void dag_node_add_dep(struct dag_node *, struct dag_node *);
int dag_sched_submit(struct dag_node *);

// RCU (Read-Copy-Update) support
void rcuinit(void);
void rcu_read_lock(void);
void rcu_read_unlock(void);
void rcu_synchronize(void);

// Memory utility
pte_t *pte_lookup(pde_t *, const void *);
void tlb_flush_page(void *);
void *atomic_cas_ptr(volatile void **, void *, void *);

// number of elements in fixed-size array
#define NELEM(x) (sizeof(x) / sizeof((x)[0]))