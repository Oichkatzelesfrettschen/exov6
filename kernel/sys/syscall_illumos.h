/**
 * @file syscall_illumos.h
 * @brief Illumos/Solaris syscall compatibility layer
 * 
 * Provides Illumos/OpenSolaris syscall definitions and structures
 * for brand zones compatibility based on illumos-gate.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include "syscall_gateway.h"

// =============================================================================
// ILLUMOS/SOLARIS SYSCALL NUMBERS
// =============================================================================

// Based on illumos-gate/usr/src/uts/common/sys/syscall.h
#define ILLUMOS_SYS_syscall         0
#define ILLUMOS_SYS_exit            1
#define ILLUMOS_SYS_read            3
#define ILLUMOS_SYS_write           4
#define ILLUMOS_SYS_open            5
#define ILLUMOS_SYS_close           6
#define ILLUMOS_SYS_linkat          7
#define ILLUMOS_SYS_link            9
#define ILLUMOS_SYS_unlink          10
#define ILLUMOS_SYS_symlinkat       11
#define ILLUMOS_SYS_chdir           12
#define ILLUMOS_SYS_time            13
#define ILLUMOS_SYS_mknod           14
#define ILLUMOS_SYS_chmod           15
#define ILLUMOS_SYS_chown           16
#define ILLUMOS_SYS_brk             17
#define ILLUMOS_SYS_stat            18
#define ILLUMOS_SYS_lseek           19
#define ILLUMOS_SYS_getpid          20
#define ILLUMOS_SYS_mount           21
#define ILLUMOS_SYS_readlinkat      22
#define ILLUMOS_SYS_setuid          23
#define ILLUMOS_SYS_getuid          24
#define ILLUMOS_SYS_stime           25
#define ILLUMOS_SYS_pcsample        26
#define ILLUMOS_SYS_alarm           27
#define ILLUMOS_SYS_fstat           28
#define ILLUMOS_SYS_pause           29
#define ILLUMOS_SYS_stty            31
#define ILLUMOS_SYS_gtty            32
#define ILLUMOS_SYS_access          33
#define ILLUMOS_SYS_nice            34
#define ILLUMOS_SYS_statfs          35
#define ILLUMOS_SYS_sync            36
#define ILLUMOS_SYS_kill            37
#define ILLUMOS_SYS_fstatfs         38
#define ILLUMOS_SYS_pgrpsys         39
#define ILLUMOS_SYS_uucopystr       40
#define ILLUMOS_SYS_dup             41
#define ILLUMOS_SYS_pipe            42
#define ILLUMOS_SYS_times           43
#define ILLUMOS_SYS_profil          44
#define ILLUMOS_SYS_faccessat       45
#define ILLUMOS_SYS_setgid          46
#define ILLUMOS_SYS_getgid          47
#define ILLUMOS_SYS_mknodat         48
#define ILLUMOS_SYS_msgsys          49  // IPC message queue
#define ILLUMOS_SYS_sysi86          50  // x86 specific
#define ILLUMOS_SYS_acct            51
#define ILLUMOS_SYS_shmsys          52  // IPC shared memory
#define ILLUMOS_SYS_semsys          53  // IPC semaphores
#define ILLUMOS_SYS_ioctl           54
#define ILLUMOS_SYS_uadmin          55
#define ILLUMOS_SYS_fchownat        56
#define ILLUMOS_SYS_utssys          57
#define ILLUMOS_SYS_fdsync          58
#define ILLUMOS_SYS_execve          59
#define ILLUMOS_SYS_umask           60
#define ILLUMOS_SYS_chroot          61
#define ILLUMOS_SYS_fcntl           62
#define ILLUMOS_SYS_ulimit          63
#define ILLUMOS_SYS_renameat        64
#define ILLUMOS_SYS_unlinkat        65
#define ILLUMOS_SYS_fstatat         66
#define ILLUMOS_SYS_fstatat64       67
#define ILLUMOS_SYS_openat          68
#define ILLUMOS_SYS_openat64        69
#define ILLUMOS_SYS_tasksys         70  // Task/project management
#define ILLUMOS_SYS_acctctl         71
#define ILLUMOS_SYS_exacctsys       72
#define ILLUMOS_SYS_getpagesizes    73
#define ILLUMOS_SYS_rctlsys         74  // Resource controls
#define ILLUMOS_SYS_sidsys          75  // SID management
#define ILLUMOS_SYS_lwp_park        77  // LWP parking
#define ILLUMOS_SYS_sendfilev       78
#define ILLUMOS_SYS_rmdir           79
#define ILLUMOS_SYS_mkdir           80
#define ILLUMOS_SYS_getdents        81
#define ILLUMOS_SYS_privsys         82  // Privilege system
#define ILLUMOS_SYS_ucredsys        83  // Credential management
#define ILLUMOS_SYS_sysfs           84
#define ILLUMOS_SYS_getmsg          85
#define ILLUMOS_SYS_putmsg          86
#define ILLUMOS_SYS_lstat           88
#define ILLUMOS_SYS_symlink         89
#define ILLUMOS_SYS_readlink        90
#define ILLUMOS_SYS_setgroups       91
#define ILLUMOS_SYS_getgroups       92
#define ILLUMOS_SYS_fchmod          93
#define ILLUMOS_SYS_fchown          94
#define ILLUMOS_SYS_sigprocmask     95
#define ILLUMOS_SYS_sigsuspend      96
#define ILLUMOS_SYS_sigaltstack     97
#define ILLUMOS_SYS_sigaction       98
#define ILLUMOS_SYS_sigpending      99
#define ILLUMOS_SYS_context         100
#define ILLUMOS_SYS_fchmodat        101
#define ILLUMOS_SYS_mkdirat         102
#define ILLUMOS_SYS_statvfs         103
#define ILLUMOS_SYS_fstatvfs        104
#define ILLUMOS_SYS_getloadavg      105
#define ILLUMOS_SYS_nfssys          106  // NFS operations
#define ILLUMOS_SYS_waitid          107
#define ILLUMOS_SYS_sigsendsys      108
#define ILLUMOS_SYS_hrtsys          109  // High-res timers
#define ILLUMOS_SYS_utimesys        110
#define ILLUMOS_SYS_sigresend       111
#define ILLUMOS_SYS_priocntlsys     112  // Priority control
#define ILLUMOS_SYS_pathconf        113
#define ILLUMOS_SYS_mincore         114
#define ILLUMOS_SYS_mmap            115
#define ILLUMOS_SYS_mprotect        116
#define ILLUMOS_SYS_munmap          117
#define ILLUMOS_SYS_fpathconf       118
#define ILLUMOS_SYS_vfork           119
#define ILLUMOS_SYS_fchdir          120
#define ILLUMOS_SYS_readv           121
#define ILLUMOS_SYS_writev          122
#define ILLUMOS_SYS_preadv          123
#define ILLUMOS_SYS_pwritev         124
#define ILLUMOS_SYS_getrandom       125
#define ILLUMOS_SYS_mmapobj         127  // Map object file
#define ILLUMOS_SYS_setrlimit       128
#define ILLUMOS_SYS_getrlimit       129
#define ILLUMOS_SYS_lchown          130
#define ILLUMOS_SYS_memcntl         131  // Memory control
#define ILLUMOS_SYS_getpmsg         132
#define ILLUMOS_SYS_putpmsg         133
#define ILLUMOS_SYS_rename          134
#define ILLUMOS_SYS_uname           135
#define ILLUMOS_SYS_setegid         136
#define ILLUMOS_SYS_sysconfig       137
#define ILLUMOS_SYS_adjtime         138
#define ILLUMOS_SYS_systeminfo      139
#define ILLUMOS_SYS_sharefs         140  // Share filesystem
#define ILLUMOS_SYS_seteuid         141
#define ILLUMOS_SYS_forksys         142  // Fork variants
#define ILLUMOS_SYS_sigtimedwait    144
#define ILLUMOS_SYS_lwp_info        145
#define ILLUMOS_SYS_yield           146
#define ILLUMOS_SYS_lwp_sema_wait   147
#define ILLUMOS_SYS_lwp_sema_post   148
#define ILLUMOS_SYS_lwp_sema_trywait 149
#define ILLUMOS_SYS_lwp_detach      150
#define ILLUMOS_SYS_corectl         151  // Core dump control
#define ILLUMOS_SYS_modctl          152  // Module control
#define ILLUMOS_SYS_fchroot         153
#define ILLUMOS_SYS_vhangup         155
#define ILLUMOS_SYS_gettimeofday    156
#define ILLUMOS_SYS_getitimer       157
#define ILLUMOS_SYS_setitimer       158
#define ILLUMOS_SYS_lwp_create      159
#define ILLUMOS_SYS_lwp_exit        160
#define ILLUMOS_SYS_lwp_suspend     161
#define ILLUMOS_SYS_lwp_continue    162
#define ILLUMOS_SYS_lwp_kill        163
#define ILLUMOS_SYS_lwp_self        164
#define ILLUMOS_SYS_lwp_sigmask     165
#define ILLUMOS_SYS_lwp_private     166
#define ILLUMOS_SYS_lwp_wait        167
#define ILLUMOS_SYS_lwp_mutex_wakeup 168
#define ILLUMOS_SYS_lwp_cond_wait   170
#define ILLUMOS_SYS_lwp_cond_signal 171
#define ILLUMOS_SYS_lwp_cond_broadcast 172
#define ILLUMOS_SYS_pread           173
#define ILLUMOS_SYS_pwrite          174
#define ILLUMOS_SYS_llseek          175
#define ILLUMOS_SYS_inst_sync       176  // Instruction cache sync
#define ILLUMOS_SYS_brand           177  // Brand operations
#define ILLUMOS_SYS_kaio            178  // Kernel async I/O
#define ILLUMOS_SYS_cpc             179  // CPU performance counters
#define ILLUMOS_SYS_lgrpsys         180  // Locality groups
#define ILLUMOS_SYS_meminfosys      181  // Memory information
#define ILLUMOS_SYS_rusagesys       182  // Resource usage
#define ILLUMOS_SYS_port            183  // Event ports
#define ILLUMOS_SYS_pollsys         184  // Poll system
#define ILLUMOS_SYS_labelsys        185  // Trusted extensions labels
#define ILLUMOS_SYS_acl             186  // ACL operations
#define ILLUMOS_SYS_auditsys        187  // Audit subsystem
#define ILLUMOS_SYS_processor_bind  188
#define ILLUMOS_SYS_processor_info  189
#define ILLUMOS_SYS_p_online        190  // Processor online/offline
#define ILLUMOS_SYS_sigqueue        191
#define ILLUMOS_SYS_clock_gettime   192
#define ILLUMOS_SYS_clock_settime   193
#define ILLUMOS_SYS_clock_getres    194
#define ILLUMOS_SYS_timer_create    195
#define ILLUMOS_SYS_timer_delete    196
#define ILLUMOS_SYS_timer_settime   197
#define ILLUMOS_SYS_timer_gettime   198
#define ILLUMOS_SYS_timer_getoverrun 199
#define ILLUMOS_SYS_nanosleep       200
#define ILLUMOS_SYS_facl            201  // File ACL
#define ILLUMOS_SYS_door            202  // Door IPC
#define ILLUMOS_SYS_setreuid        203
#define ILLUMOS_SYS_setregid        204
#define ILLUMOS_SYS_install_utrap   205  // SPARC user trap
#define ILLUMOS_SYS_signotify       206
#define ILLUMOS_SYS_schedctl        207  // Scheduler control
#define ILLUMOS_SYS_pset            208  // Processor sets
#define ILLUMOS_SYS_sparc_utrap_install 209
#define ILLUMOS_SYS_resolvepath     210
#define ILLUMOS_SYS_lwp_mutex_timedlock 211
#define ILLUMOS_SYS_lwp_sema_timedwait 212
#define ILLUMOS_SYS_lwp_rwlock_sys  213
#define ILLUMOS_SYS_getdents64      214
#define ILLUMOS_SYS_mmap64          215
#define ILLUMOS_SYS_stat64          216
#define ILLUMOS_SYS_lstat64         217
#define ILLUMOS_SYS_fstat64         218
#define ILLUMOS_SYS_statvfs64       219
#define ILLUMOS_SYS_fstatvfs64      220
#define ILLUMOS_SYS_setrlimit64     221
#define ILLUMOS_SYS_getrlimit64     222
#define ILLUMOS_SYS_pread64         223
#define ILLUMOS_SYS_pwrite64        224
#define ILLUMOS_SYS_open64          225
#define ILLUMOS_SYS_zone            227  // Zone operations
#define ILLUMOS_SYS_getzoneid       228
#define ILLUMOS_SYS_getcwd          229
#define ILLUMOS_SYS_so_socket       230  // Socket operations
#define ILLUMOS_SYS_so_socketpair   231
#define ILLUMOS_SYS_bind            232
#define ILLUMOS_SYS_listen          233
#define ILLUMOS_SYS_accept          234
#define ILLUMOS_SYS_connect         235
#define ILLUMOS_SYS_shutdown        236
#define ILLUMOS_SYS_recv            237
#define ILLUMOS_SYS_recvfrom        238
#define ILLUMOS_SYS_recvmsg         239
#define ILLUMOS_SYS_send            240
#define ILLUMOS_SYS_sendmsg         241
#define ILLUMOS_SYS_sendto          242
#define ILLUMOS_SYS_getpeername     243
#define ILLUMOS_SYS_getsockname     244
#define ILLUMOS_SYS_getsockopt      245
#define ILLUMOS_SYS_setsockopt      246
#define ILLUMOS_SYS_sockconfig      247
#define ILLUMOS_SYS_ntp_gettime     248
#define ILLUMOS_SYS_ntp_adjtime     249
#define ILLUMOS_SYS_lwp_mutex_unlock 250
#define ILLUMOS_SYS_lwp_mutex_trylock 251
#define ILLUMOS_SYS_lwp_mutex_register 252
#define ILLUMOS_SYS_cladm           253  // Cluster admin
#define ILLUMOS_SYS_uucopy          254
#define ILLUMOS_SYS_umount2         255

#define ILLUMOS_SYS_MAX             256

// =============================================================================
// ILLUMOS-SPECIFIC STRUCTURES
// =============================================================================

// Illumos stat structure (different field ordering from POSIX)
struct illumos_stat {
    uint64_t st_dev;
    uint64_t st_ino;
    uint32_t st_mode;
    uint32_t st_nlink;
    uint32_t st_uid;
    uint32_t st_gid;
    uint64_t st_rdev;
    int64_t  st_size;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_atim;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_mtim;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_ctim;
    int32_t  st_blksize;
    int64_t  st_blocks;
    char     st_fstype[16];  // Illumos-specific: filesystem type
};

// Zone information structure
struct illumos_zone_info {
    int32_t  zone_id;
    char     zone_name[64];
    char     zone_root[256];
    uint32_t zone_state;
    uint32_t zone_flags;
};

// Door IPC structure (unique to Illumos)
struct illumos_door_arg {
    void    *data_ptr;
    size_t   data_size;
    void    *desc_ptr;
    uint32_t desc_num;
    void    *rbuf;
    size_t   rsize;
};

// LWP (Lightweight Process) info
struct illumos_lwpinfo {
    int32_t  lwp_id;
    uint32_t lwp_flags;
    void    *lwp_ustack;
    size_t   lwp_stacksize;
    void    *lwp_private;
};

// =============================================================================
// ILLUMOS FLAG DEFINITIONS
// =============================================================================

// File open flags (some Illumos-specific)
#define ILLUMOS_O_RDONLY     0x0000
#define ILLUMOS_O_WRONLY     0x0001
#define ILLUMOS_O_RDWR       0x0002
#define ILLUMOS_O_SEARCH     0x0200  // Illumos: directory search
#define ILLUMOS_O_EXEC       0x0400  // Illumos: execute only
#define ILLUMOS_O_CREAT      0x0100
#define ILLUMOS_O_TRUNC      0x0200
#define ILLUMOS_O_EXCL       0x0400
#define ILLUMOS_O_NOCTTY     0x0800
#define ILLUMOS_O_XATTR      0x4000  // Illumos: extended attributes

// Zone states
#define ILLUMOS_ZONE_STATE_CONFIGURED    0
#define ILLUMOS_ZONE_STATE_INCOMPLETE    1
#define ILLUMOS_ZONE_STATE_INSTALLED     2
#define ILLUMOS_ZONE_STATE_READY         3
#define ILLUMOS_ZONE_STATE_RUNNING       4
#define ILLUMOS_ZONE_STATE_SHUTTING_DOWN 5
#define ILLUMOS_ZONE_STATE_DOWN          6

// =============================================================================
// FUNCTION PROTOTYPES
// =============================================================================

// Initialize Illumos personality
void illumos_personality_init(void);

// Syscall handlers
long sys_illumos_zone(int cmd, void *arg, void *arg2, void *arg3, void *arg4);
long sys_illumos_door(int subcode, void *arg);
long sys_illumos_lwp_create(struct illumos_lwpinfo *lwp, int flags, void *stack);
long sys_illumos_brand(int cmd, void *arg);
long sys_illumos_privsys(int cmd, void *arg1, void *arg2, void *arg3);

// Translation functions
int translate_illumos_open_flags(int flags);
int translate_illumos_stat(void *src, void *dst, int direction);
int translate_illumos_errno(int native_errno);

// Compatibility helpers
int illumos_getzoneid(void);
int illumos_zone_enter(int zoneid);
int illumos_door_create(void (*server_proc)(void *), void *cookie, uint32_t flags);
int illumos_door_call(int door_fd, struct illumos_door_arg *arg);

// Extended attributes (Illumos-specific)
int illumos_openat(int fd, const char *path, int flags, mode_t mode);
int illumos_fgetattr(int fd, const char *attr, void *buf, size_t size);
int illumos_fsetattr(int fd, const char *attr, const void *buf, size_t size);

// Processor sets (Illumos-specific)
int illumos_pset_create(int *psetid);
int illumos_pset_destroy(int psetid);
int illumos_pset_bind(int psetid, int what, int id, int *old_psetid);

// Event ports (Illumos-specific)
int illumos_port_create(void);
int illumos_port_associate(int port, int source, uintptr_t object, int events, void *user);
int illumos_port_get(int port, void *event, struct timespec *timeout);

// =============================================================================
// SYSCALL TABLE DECLARATION
// =============================================================================

extern const syscall_entry_t illumos_syscall_table[];
extern const unsigned int illumos_syscall_table_size;

#endif // SYSCALL_ILLUMOS_H