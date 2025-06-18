
#pragma once

#include "types.h"
#include "param.h"
#include <compiler_attrs.h>
#if __has_include("config.h")
#include "config.h"
#endif
#include "spinlock.h"
#include "proc.h"
#include "ipc.h"
#include "cap.h"
#include "service.h"
#include <stdnoreturn.h>

struct buf;
struct context;
#if defined(__x86_64__) || defined(__aarch64__)
struct context64;
typedef struct context64 context_t;
#else
typedef struct context context_t;
#endif
#define EXO_CONTEXT_T
struct file;
struct inode;
struct pipe;
struct proc;
struct trapframe;
struct rtcdate;
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

// process table defined in proc.c
extern struct ptable ptable;
extern struct spinlock sched_lock;

#include "exo_cpu.h"
#include "exo_disk.h"
#include "exo_ipc.h"
#include "fastipc.h"

// bio.c
void binit(void);
struct buf *bread(uint32_t, uint32_t);
void brelse(struct buf *);
void bwrite(struct buf *);

// console.c
void consoleinit(void);
void cprintf(char *, ...);
void consoleintr(int (*)(void));
_Noreturn void panic(char *);

// exec.c
int exec(char *, char **);

// file.c

struct file *filealloc(void);
void fileclose(struct file *);
struct file *filedup(struct file *);
void fileinit(void);
int fileread(struct file *, char *, size_t n);
int filestat(struct file *, struct stat *);
int filewrite(struct file *, char *, size_t n);

// fs.c
void readsb(int dev, struct superblock *sb);
int dirlink(struct inode *, char *, uint32_t);
struct inode *dirlookup(struct inode *, char *, uint32_t *);
struct inode *ialloc(uint32_t, short);
struct inode *idup(struct inode *);
void iinit(int dev);
void ilock(struct inode *);
void iput(struct inode *);
void iunlock(struct inode *);
void iunlockput(struct inode *);
void iupdate(struct inode *);
int namecmp(const char *, const char *);
struct inode *namei(char *);
struct inode *nameiparent(char *, char *);
int readi(struct inode *, char *, uint32_t, size_t);
void stati(struct inode *, struct stat *);
int writei(struct inode *, char *, uint32_t, size_t);

// ide.c
void ideinit(void);
void ideintr(void);
void iderw(struct buf *);

// ioapic.c
void ioapicenable(int irq, int cpu);
extern uint8_t ioapicid;
void ioapicinit(void);

// kalloc.c
char *kalloc(void);
void kfree(char *);
void kinit1(void *, void *);
void kinit2(void *, void *);

// kbd.c
void kbdintr(void);

// lapic.c
void cmostime(struct rtcdate *r);
int lapicid(void);
extern volatile uint32_t *lapic;
void lapiceoi(void);
void lapicinit(void);
void lapicstartap(uint8_t, uint32_t);
void microdelay(int);

// log.c
void initlog(int dev);
void log_write(struct buf *);
void begin_op();
void end_op();

// mp.c
extern int ismp;
void mpinit(void);

// picirq.c
void picenable(int);
void picinit(void);

// pipe.c

EXO_NODISCARD int pipealloc(struct file **, struct file **);
void pipeclose(struct pipe *, int);
int piperead(struct pipe *, struct file *, char *, size_t);
int pipewrite(struct pipe *, struct file *, char *, size_t);

// PAGEBREAK: 16
//  proc.c
int cpuid(void);
void exit(void);
int fork(void);
int growproc(int);
int kill(int);
int sigsend(int, int);
struct cpu *mycpu(void);
struct proc *myproc();
void pinit(void);
void procdump(void);
_Noreturn void scheduler(void);
void sched(void);
void setproc(struct proc *);
void sleep(void *, struct spinlock *);
void userinit(void);
int wait(void);
void wakeup(void *);
void yield(void);
struct proc *pctr_lookup(uint32_t);
struct proc *allocproc(void);

// swtch.S
void swtch(context_t **, context_t *);

// spinlock.c
void acquire(struct spinlock *);
void getcallerpcs(void *, uint32_t *);
int holding(struct spinlock *);
void initlock(struct spinlock *, char *);
void release(struct spinlock *);
void pushcli(void);
void popcli(void);
void qspin_lock(struct spinlock *);
void qspin_unlock(struct spinlock *);
int qspin_trylock(struct spinlock *);

// sleeplock.c
void acquiresleep(struct sleeplock *);
void releasesleep(struct sleeplock *);
int holdingsleep(struct sleeplock *);
void initsleeplock(struct sleeplock *, char *);

// string.c

char *safestrcpy(char *, const char *, size_t);

// syscall.c
int argint(int, int *);
int argptr(int, char **, size_t);
int argstr(int, char **);
int fetchint(uintptr_t, int *);
int fetchstr(uintptr_t, char **);
void syscall(void);

// timer.c
void timerinit(void);

// trap.c
void idtinit(void);
extern uint32_t ticks;
void tvinit(void);
extern struct spinlock tickslock;
void exo_pctr_transfer(struct trapframe *);

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
int allocuvm(pde_t *, uint32_t, uint32_t);
int deallocuvm(pde_t *, uint32_t, uint32_t);
void freevm(pde_t *);
void inituvm(pde_t *, char *, uint32_t);
int loaduvm(pde_t *, char *, struct inode *, uint32_t, uint32_t);
pde_t *copyuvm(pde_t *, uint32_t);
void switchuvm(struct proc *);
void switchkvm(void);
#ifdef __x86_64__
int copyout(pde_t *, uint64_t, void *, uint32_t);
#else
int copyout(pde_t *, uint32_t, void *, uint32_t);
#endif

void clearpteu(pde_t *pgdir, char *uva);
#ifdef __x86_64__
int insert_pte(pde_t *, void *, uint64_t, int);
#else
int insert_pte(pde_t *, void *, uint32_t, int);
#endif
exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap);
exo_cap cap_new(uint32_t id, uint32_t rights, uint32_t owner);
int cap_verify(exo_cap);
struct exo_blockcap exo_alloc_block(uint32_t dev, uint32_t rights);
int exo_bind_block(struct exo_blockcap *, struct buf *, int);
void exo_flush_block(struct exo_blockcap *, void *);
exo_cap exo_alloc_irq(uint32_t irq, uint32_t rights);
int exo_irq_wait(exo_cap cap, uint32_t *irq);
int exo_irq_ack(exo_cap cap);
int irq_trigger(uint32_t irq);
exo_cap exo_alloc_ioport(uint32_t port);
exo_cap exo_bind_irq(uint32_t irq);
exo_cap exo_alloc_dma(uint32_t chan);
exo_cap exo_alloc_hypervisor(void);
int hv_launch_guest(exo_cap cap, const char *path);
void cap_table_init(void);
int cap_table_alloc(uint16_t type, uint32_t resource, uint32_t rights,
                    uint32_t owner);
int cap_table_lookup(cap_id_t id, struct cap_entry *out);
void cap_table_inc(cap_id_t id);
void cap_table_dec(cap_id_t id);
int cap_table_remove(cap_id_t id);

// service.c
int service_register(const char *name, const char *path,
                     service_options_t opts);
int service_add_dependency(const char *name, const char *dependency);
void service_notify_exit(struct proc *p);
void exo_stream_register(struct exo_stream *);
void exo_stream_halt(void);
void exo_stream_yield(void);
void dag_sched_init(void);
void beatty_sched_init(void);

struct exo_sched_ops *dag_sched_ops(void);
struct exo_sched_ops *beatty_sched_ops(void);
void beatty_dag_stream_init(void);
void beatty_sched_set_tasks(const exo_cap *, const double *, int);
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

// rcu.c
void rcuinit(void);
void rcu_read_lock(void);
void rcu_read_unlock(void);
void rcu_synchronize(void);

// memutil.c
pte_t *pte_lookup(pde_t *, const void *);
void tlb_flush_page(void *);
void *atomic_cas_ptr(volatile void **, void *, void *);

// number of elements in fixed-size array
#define NELEM(x) (sizeof(x) / sizeof((x)[0]))
