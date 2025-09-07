#pragma once

/**
 * @file sys/wait.h
 * @brief Process wait operations
 */

#include <sys/types.h>
#include <stdint.h>

// Wait options
#define WNOHANG    0x01
#define WUNTRACED  0x02
#define WCONTINUED 0x08

// Status macros
#define WIFEXITED(s)    (!((s) & 0x7f))
#define WEXITSTATUS(s)  (((s) >> 8) & 0xff)
#define WIFSIGNALED(s)  (((s) & 0x7f) && !((s) & 0x80))
#define WTERMSIG(s)     ((s) & 0x7f)
#define WIFSTOPPED(s)   (((s) & 0xff) == 0x7f)
#define WSTOPSIG(s)     (((s) >> 8) & 0xff)
#define WIFCONTINUED(s) ((s) == 0xffff)

// Wait ID types
typedef enum {
    P_ALL,
    P_PID,
    P_PGID
} idtype_t;

// Function declarations
pid_t wait(int* wstatus);
pid_t waitpid(pid_t pid, int* wstatus, int options);
int waitid(idtype_t idtype, id_t id, siginfo_t* infop, int options);