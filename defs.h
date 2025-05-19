struct buf;
struct context;
#ifdef __x86_64__
struct context64;
typedef struct context64 context_t;
#else
typedef struct context context_t;
#endif
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

#include "kernel/exo_cpu.h"
#include "kernel/exo_disk.h"
#include "kernel/exo_ipc.h"
#include "kernel/exo_mem.h"

// bio.c
void binit(void);
struct buf *bread(uint, uint);
void brelse(struct buf *);
void bwrite(struct buf *);

// console.c
void consoleinit(void);
void cprintf(char *, ...);
void consoleintr(int (*)(void));
void panic(char *) __attribute__((noreturn));

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
int dirlink(struct inode *, char *, uint);
struct inode *dirlookup(struct inode *, char *, uint *);
struct inode *ialloc(uint, short);
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
int readi(struct inode *, char *, uint, uint);
void stati(struct inode *, struct stat *);
int writei(struct inode *, char *, uint, uint);

// ide.c
void ideinit(void);
void ideintr(void);
void iderw(struct buf *);

// ioapic.c
void ioapicenable(int irq, int cpu);
extern uchar ioapicid;
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
extern volatile uint *lapic;
void lapiceoi(void);
void lapicinit(void);
void lapicstartap(uchar, uint);
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
int pipealloc(struct file **, struct file **);
void pipeclose(struct pipe *, int);
int piperead(struct pipe *, char *, size_t);
int pipewrite(struct pipe *, char *, size_t);

// PAGEBREAK: 16
//  proc.c
int cpuid(void);
void exit(void);
int fork(void);
int growproc(int);
int kill(int);
struct cpu *mycpu(void);
struct proc *myproc();
void pinit(void);
void procdump(void);
void scheduler(void) __attribute__((noreturn));
void sched(void);
void setproc(struct proc *);
void sleep(void *, struct spinlock *);
void userinit(void);
int wait(void);
void wakeup(void *);
void yield(void);

// swtch.S
void swtch(context_t **, context_t *);

// spinlock.c
void acquire(struct spinlock *);
void getcallerpcs(void *, uint *);
int holding(struct spinlock *);
void initlock(struct spinlock *, char *);
void release(struct spinlock *);
void pushcli(void);
void popcli(void);

// sleeplock.c
void acquiresleep(struct sleeplock *);
void releasesleep(struct sleeplock *);
int holdingsleep(struct sleeplock *);
void initsleeplock(struct sleeplock *, char *);

// string.c
int memcmp(const void *, const void *, size_t);
void *memmove(void *, const void *, size_t);
void *memset(void *, int, size_t);
char *safestrcpy(char *, const char *, size_t);
size_t strlen(const char *);
int strncmp(const char *, const char *, size_t);
char *strncpy(char *, const char *, size_t);

// syscall.c
int argint(int, int *);
int argptr(int, char **, size_t);
int argstr(int, char **);
int fetchint(uint, int *);
int fetchstr(uint, char **);
void syscall(void);

// timer.c
void timerinit(void);

// trap.c
void idtinit(void);
extern uint ticks;
void tvinit(void);
extern struct spinlock tickslock;
void            exo_pctr_transfer(struct trapframe *);

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
int allocuvm(pde_t *, uint, uint);
int deallocuvm(pde_t *, uint, uint);
void freevm(pde_t *);
void inituvm(pde_t *, char *, uint);
int loaduvm(pde_t *, char *, struct inode *, uint, uint);
pde_t *copyuvm(pde_t *, uint);
void switchuvm(struct proc *);
void switchkvm(void);
#ifdef __x86_64__
int insert_pte(pde_t *, void *, uint64, int);
#else
int insert_pte(pde_t *, void *, uint, int);
#endif
#ifdef __x86_64__
int copyout(pde_t *, uint64, void *, uint);
#else
int copyout(pde_t *, uint, void *, uint);
#endif

void            clearpteu(pde_t *pgdir, char *uva);
struct exo_cap  exo_alloc_page(void);
int             exo_unbind_page(struct exo_cap);
int             exo_alloc_block(uint dev, struct exo_blockcap *);
int             exo_bind_block(struct exo_blockcap *, void *, int);


// number of elements in fixed-size array
#define NELEM(x) (sizeof(x) / sizeof((x)[0]))
