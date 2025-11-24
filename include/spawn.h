/**
 * @file spawn.h
 * @brief User-Space Process Spawning Interface (Phase 11)
 *
 * EXOKERNEL PROCESS CREATION:
 *
 *   spawn() is the LIBOS way of creating processes.
 *   Unlike UNIX fork()+exec(), spawn() does everything in user space:
 *
 *   1. Open ELF file via IPC to fs_srv
 *   2. Create blank environment (sys_env_create)
 *   3. Load ELF segments into child's address space
 *   4. Set up argc/argv on child's stack
 *   5. Start execution (sys_env_run)
 *
 *   The kernel is IGNORANT of ELF files, arguments, and process semantics.
 *   We define all of that here in the LibOS.
 */

#ifndef SPAWN_H
#define SPAWN_H

/**
 * spawn() - Create a new process from an ELF executable
 *
 * This is the primary process creation primitive in ExoV6.
 * It combines UNIX's fork() and exec() into a single operation.
 *
 * @param path   Path to ELF executable (resolved via fs_srv IPC)
 * @param argv   NULL-terminated array of argument strings
 *               argv[0] should be the program name
 *
 * @return       Child's PID on success (>= 0), negative on error
 *
 * Example:
 *   char *args[] = {"echo", "hello", "world", NULL};
 *   int pid = spawn("/bin/echo", args);
 *   if (pid < 0) {
 *       print("spawn failed\n");
 *   }
 *
 * Error codes:
 *   -1  File not found or read error
 *   -2  Invalid ELF format
 *   -3  Out of memory
 *   -4  Environment creation failed
 *
 * LESSON: Unlike fork(), spawn() does NOT copy the parent's address space.
 * The child starts fresh with only the ELF's code/data and its arguments.
 * This is cleaner and more efficient for most use cases.
 */
int spawn(const char *path, char **argv);

/**
 * spawnl() - Spawn with inline arguments
 *
 * Convenience wrapper that takes arguments inline.
 * The argument list MUST end with NULL.
 *
 * @param path  Path to ELF executable
 * @param arg0  First argument (typically program name)
 * @param ...   Additional arguments, terminated by NULL
 *
 * @return      Child's PID on success, negative on error
 *
 * Example:
 *   int pid = spawnl("/bin/echo", "echo", "hello", "world", NULL);
 *
 * Note: Currently limited to 8 arguments due to simple implementation.
 */
int spawnl(const char *path, const char *arg0, ...);

/**
 * spawnp() - Spawn with pipe redirection
 *
 * Creates a child process with stdin/stdout redirected to pipes.
 * Essential for shell pipelines: "cmd1 | cmd2"
 *
 * @param path        Path to ELF executable
 * @param argv        NULL-terminated argument array
 * @param stdin_pipe  Pipe ID for stdin (-1 for no redirection)
 * @param stdout_pipe Pipe ID for stdout (-1 for no redirection)
 *
 * @return            Child's PID on success, negative on error
 *
 * Example (for "echo hello | cat"):
 *   int pfd[2];
 *   fd_pipe(pfd);
 *   // pfd[0] = read end, pfd[1] = write end
 *   // Need to get underlying pipe_id from fd layer
 *   spawnp("/echo", argv1, -1, pipe_id);   // stdout → pipe
 *   spawnp("/cat",  argv2, pipe_id, -1);   // stdin ← pipe
 *
 * The pipe buffer is mapped into child's address space so it can
 * directly read/write without additional IPC.
 */
int spawnp(const char *path, char **argv, int stdin_pipe, int stdout_pipe);

#endif /* SPAWN_H */
