/* Phoenix Exokernel POSIX compatibility layer */
#include <fcntl.h>        /* O_TRUNC, O_APPEND constants - must come first */
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>       /* memset, strlen */

/* Ensure O_TRUNC and O_APPEND are defined */
#ifndef O_TRUNC
#define O_TRUNC    0x0200
#endif
#ifndef O_APPEND 
#define O_APPEND   0x0008
#endif

/* Minimal type definitions to avoid header conflicts */
#ifndef __STDINT_TYPES_DEFINED
#define __STDINT_TYPES_DEFINED
#include <stdint.h>  /* Use system stdint.h */
#endif

#ifndef __SIZE_T_DEFINED
#define __SIZE_T_DEFINED
#include <stddef.h>  /* Use system stddef.h */
#endif

/* File structure definition to avoid header conflicts */
struct file {
  enum { FD_NONE, FD_PIPE, FD_INODE } type;
  size_t ref; // reference count
  char readable;
  char writable;
  struct pipe *pipe;
  struct inode *ip;
  size_t off;
  int flags;
};

/* Forward declarations to avoid including problem headers */
struct pipe;
struct inode;
struct sleeplock;

typedef struct exo_cap {
    uint32_t pa;
    uint32_t id; 
    uint32_t rights;
    uint32_t owner;
    uint64_t auth_tag[4];
} exo_cap;

/* Function declarations we need */
int exec(char *path, char **argv);
int sigsend(int pid, int sig);
int sigcheck(void);
void *malloc(size_t size);
void free(void *ptr);
void *realloc(void *ptr, size_t size);
void *calloc(size_t nmemb, size_t size);

/* POSIX function signatures for libOS layer */
typedef unsigned long libos_sigset_t;

/* Define struct sigaction to avoid conflicts */
#ifndef SA_NOCLDSTOP
typedef unsigned long sigset_t;  /* Use same as libos_sigset_t */
struct sigaction { 
    void (*sa_handler)(int); 
    sigset_t sa_mask;
    int sa_flags;
};
#endif

/* Phoenix libOS functions - declare directly to avoid header conflicts */
struct file *libfs_open(const char *path, int flags);
int libfs_read(struct file *f, void *buf, size_t n);
int libfs_write(struct file *f, const void *buf, size_t n);
void libfs_close(struct file *f);
int libfs_truncate(struct file *f, size_t length);
int libfs_unlink(const char *path);
int libfs_rename(const char *oldpath, const char *newpath);
int filestat(struct file *f, struct stat *st);
struct file *filedup(struct file *f);
void fileclose(struct file *f);

/* Exokernel capability functions */
exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap cap);

#define LIBOS_INITFD 16

static struct file **fd_table;
static int fd_table_cap = 0;

static void ensure_fd_table(void) {
  if (!fd_table) {
    fd_table_cap = LIBOS_INITFD;
    fd_table = calloc(fd_table_cap, sizeof(struct file *));
  }
}
static void (*sig_handlers[32])(int);

typedef struct {
  void *addr;
  size_t len;
  exo_cap cap;
} mmap_entry_t;

static mmap_entry_t *mmap_table;
static int mmap_cap = 0;
static int mmap_count = 0;

static void mmap_table_add(void *addr, size_t len, exo_cap cap) {
  if (mmap_count == mmap_cap) {
    int new_cap = mmap_cap ? mmap_cap * 2 : 4;
    mmap_entry_t *nt = realloc(mmap_table, new_cap * sizeof(mmap_entry_t));
    if (!nt)
      return;
    mmap_table = nt;
    mmap_cap = new_cap;
  }
  mmap_table[mmap_count].addr = addr;
  mmap_table[mmap_count].len = len;
  mmap_table[mmap_count].cap = cap;
  mmap_count++;
}

static int mmap_table_remove(void *addr, exo_cap *out) {
  for (int i = 0; i < mmap_count; i++) {
    if (mmap_table[i].addr == addr) {
      if (out)
        *out = mmap_table[i].cap;
      mmap_count--;
      mmap_table[i] = mmap_table[mmap_count];
      return 0;
    }
  }
  return -1;
}

int libos_open(const char *path, int flags, int mode) {
  (void)mode; /* mode ignored by simple filesystem */
  ensure_fd_table();
  struct file *f = libfs_open(path, flags);
  if (!f)
    return -1;
  if (flags & O_TRUNC) {
    libfs_truncate(f, 0);
  }
  if (flags & O_APPEND) {
    struct stat st;
    if (filestat(f, &st) == 0)
      f->off = st.st_size;
  }
  for (int i = 0; i < fd_table_cap; i++) {
    if (!fd_table[i]) {
      fd_table[i] = f;
      return i;
    }
  }
  int new_cap = fd_table_cap * 2;
  struct file **nt = realloc(fd_table, new_cap * sizeof(struct file *));
  if (!nt) {
    fileclose(f);
    return -1;
  }
  memset(nt + fd_table_cap, 0,
         (new_cap - fd_table_cap) * sizeof(struct file *));
  fd_table = nt;
  int idx = fd_table_cap;
  fd_table_cap = new_cap;
  fd_table[idx] = f;
  return idx;
}

int libos_read(int fd, void *buf, size_t n) {
  ensure_fd_table();
  if (fd < 0 || fd >= fd_table_cap || !fd_table[fd])
    return read(fd, buf, n);
  return libfs_read(fd_table[fd], buf, n);
}

int libos_write(int fd, const void *buf, size_t n) {
  ensure_fd_table();
  if (fd < 0 || fd >= fd_table_cap || !fd_table[fd])
    return write(fd, buf, n);
  return libfs_write(fd_table[fd], buf, n);
}

int libos_close(int fd) {
  ensure_fd_table();
  if (fd >= 0 && fd < fd_table_cap && fd_table[fd]) {
    libfs_close(fd_table[fd]);
    fd_table[fd] = 0;
    return 0;
  }
  return close(fd);
}

int libos_spawn(const char *path, char *const argv[]) {
  int pid = fork();
  if (pid == 0) {
    exec((char *)path, (char **)argv);
    exit(1);
  }
  return pid;
}

int libos_execve(const char *path, char *const argv[], char *const envp[]) {
  (void)envp;
  return exec((char *)path, (char **)argv);
}

int libos_mkdir(const char *path) { return mkdir(path, 0777); }

int libos_rmdir(const char *path) { return unlink((char *)path); }

int libos_unlink(const char *path) { return libfs_unlink(path); }

int libos_rename(const char *oldpath, const char *newpath) {
  return libfs_rename(oldpath, newpath);
}

int libos_dup(int fd) {
  ensure_fd_table();
  if (fd < 0 || fd >= fd_table_cap || !fd_table[fd])
    return -1;
  struct file *f = filedup(fd_table[fd]);
  for (int i = 0; i < fd_table_cap; i++) {
    if (!fd_table[i]) {
      fd_table[i] = f;
      return i;
    }
  }
  int new_cap = fd_table_cap * 2;
  struct file **nt = realloc(fd_table, new_cap * sizeof(struct file *));
  if (!nt) {
    fileclose(f);
    return -1;
  }
  memset(nt + fd_table_cap, 0,
         (new_cap - fd_table_cap) * sizeof(struct file *));
  fd_table = nt;
  int idx = fd_table_cap;
  fd_table_cap = new_cap;
  fd_table[idx] = f;
  return idx;
}

int libos_pipe(int fd[2]) { return pipe(fd); }

int libos_fork(void) { return fork(); }

int libos_waitpid(int pid, int *status, int flags) {
  (void)flags;
  int w;
  if (pid == -1) {
    w = wait(NULL);
    if (w >= 0 && status)
      *status = 0;
    return w;
  }
  while ((w = wait(NULL)) >= 0) {
    if (w == pid) {
      if (status)
        *status = 0;
      return w;
    }
  }
  return -1;
}

int libos_sigsend(int pid, int sig) { return sigsend(pid, sig); }

int libos_sigcheck(void) {
  int pending = sigcheck();
  for (int s = 0; s < 32; s++) {
    if ((pending & (1 << s)) && sig_handlers[s])
      sig_handlers[s](s);
  }
  return pending;
}

int libos_signal(int sig, void (*handler)(int)) {
  if (sig < 0 || sig >= 32)
    return -1;
  sig_handlers[sig] = handler;
  return 0;
}

int libos_sigaction(int sig, const struct sigaction *act,
                    struct sigaction *oact) {
  if (sig < 0 || sig >= 32)
    return -1;
  if (oact) {
    memset(oact, 0, sizeof(*oact));
    oact->sa_handler = sig_handlers[sig];
  }
  if (act)
    sig_handlers[sig] = act->sa_handler;
  return 0;
}

int libos_sigprocmask(int how, const libos_sigset_t *set, libos_sigset_t *old) {
  static libos_sigset_t cur;
  if (old)
    *old = cur;
  if (!set)
    return 0;
  switch (how) {
  case 0: /* SIG_BLOCK */
    cur |= *set;
    break;
  case 1: /* SIG_UNBLOCK */
    cur &= ~(*set);
    break;
  case 2: /* SIG_SETMASK */
    cur = *set;
    break;
  default:
    return -1;
  }
  return 0;
}

int libos_killpg(int pgrp, int sig) { return sigsend(pgrp, sig); }

int libos_stat(const char *path, struct stat *st) {
  struct file *f = libfs_open(path, 0);
  if (!f)
    return -1;
  int r = filestat(f, st);
  libfs_close(f);
  return r;
}

long libos_lseek(int fd, long off, int whence) {
  ensure_fd_table();
  if (fd < 0 || fd >= fd_table_cap || !fd_table[fd])
    return -1;
  struct file *f = fd_table[fd];
  switch (whence) {
  case 0: /* SEEK_SET */
    f->off = off;
    break;
  case 1: /* SEEK_CUR */
    f->off += off;
    break;
  case 2: {
    struct stat st;
    if (filestat(f, &st) < 0)
      return -1;
    f->off = st.st_size + off;
    break;
  }
  default:
    return -1;
  }
  return f->off;
}

int libos_ftruncate(int fd, long length) {
  ensure_fd_table();
  if (fd < 0 || fd >= fd_table_cap || !fd_table[fd])
    return -1;
  if (length < 0)
    return -1;
  return libfs_truncate(fd_table[fd], (size_t)length);
}

void *libos_mmap(void *addr, size_t len, int prot, int flags, int fd,
                 long off) {
  (void)addr;
  (void)prot;
  (void)flags;
  (void)fd;
  (void)off;
  void *p = malloc(len);
  if (!p)
    return (void *)-1;
  exo_cap cap = exo_alloc_page();
  mmap_table_add(p, len, cap);
  return p;
}

int libos_munmap(void *addr, size_t len) {
  (void)len;
  exo_cap cap;
  if (mmap_table_remove(addr, &cap) == 0)
    (void)exo_unbind_page(cap);
  free(addr);
  return 0;
}

int libos_sigemptyset(libos_sigset_t *set) {
  *set = 0;
  return 0;
}
int libos_sigfillset(libos_sigset_t *set) {
  *set = ~0UL;
  return 0;
}
int libos_sigaddset(libos_sigset_t *set, int sig) {
  if (sig < 0 || sig >= 32)
    return -1;
  *set |= (1UL << sig);
  return 0;
}
int libos_sigdelset(libos_sigset_t *set, int sig) {
  if (sig < 0 || sig >= 32)
    return -1;
  *set &= ~(1UL << sig);
  return 0;
}
int libos_sigismember(const libos_sigset_t *set, int sig) {
  if (sig < 0 || sig >= 32)
    return 0;
  return (*set & (1UL << sig)) != 0;
}

int libos_getpgrp(void) { return (int)getpgrp(); }

int libos_setpgid(int pid, int pgid) { return setpgid(pid, pgid); }

int libos_socket(int domain, int type, int protocol) {
  return socket(domain, type, protocol);
}

int libos_bind(int fd, const struct sockaddr *addr, socklen_t len) {
  return bind(fd, addr, len);
}

int libos_listen(int fd, int backlog) { return listen(fd, backlog); }

int libos_accept(int fd, struct sockaddr *addr, socklen_t *len) {
  return accept(fd, addr, len);
}

int libos_connect(int fd, const struct sockaddr *addr, socklen_t len) {
  return connect(fd, addr, len);
}

long libos_send(int fd, const void *buf, size_t len, int flags) {
  return send(fd, buf, len, flags);
}

long libos_recv(int fd, void *buf, size_t len, int flags) {
  return recv(fd, buf, len, flags);
}

int libos_chdir(const char *path) { return chdir(path); }

char *libos_getcwd(char *buf, size_t size) { return getcwd(buf, size); }
