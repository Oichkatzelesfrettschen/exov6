#pragma once

#include <stddef.h>  // For size_t
#include <types.h>

// Missing types
typedef int pid_t;
#define NULL ((void*)0)
#define PATH_MAX 256

// Minimal user space header for Phase 2/3 utilities
// Avoids complex exokernel types that aren't implemented yet

struct stat {
    short type;  // Type of file
    int dev;     // File system's disk device
    uint ino;    // Inode number
    short nlink; // Number of links to file
    uint size;   // Size of file in bytes
};

// File types (must match what test_working.c expects)
#define T_DIR  1   // Directory
#define T_FILE 2   // File
#define T_DEV  3   // Device

// System calls - minimal working set  
int fork(void);
void exit(int status) __attribute__((noreturn));
int wait(int *status);
int pipe(int *);
int write(int, const void *, int);  // Simplified - use int instead of size_t
int read(int, void *, int);         // Simplified - use int instead of size_t
int close(int);
int kill(int);
int exec(const char *, char **);
int open(const char *, int);
int mknod(const char *, short, short);
int unlink(const char *);
int fstat(int fd, struct stat *);
int link(const char *, const char *);
int mkdir(const char *);
int chdir(const char *);
int dup(int);
int getpid(void);
char* sbrk(int);
int sleep(int);
int uptime(void);
int stat(const char *name, struct stat *st);
int getcwd(char *buf, int size);   // Simplified

// Directory entry structure
struct dirent {
    uint ino;
    char name[14];  // DIRSIZ
};

#define DIRSIZ 14

// File open flags
#define O_RDONLY  0x000
#define O_WRONLY  0x001  
#define O_RDWR    0x002
#define O_CREATE  0x200

// String functions - basic implementations
int strcmp(const char *, const char *);
int strncmp(const char *, const char *, size_t);
char *strcpy(char *, const char *);
char *strncpy(char *, const char *, size_t);
char *strcat(char *, const char *);
void *memmove(void *, const void *, size_t);
char *strchr(const char *, int c);
char *strrchr(const char *, int c);
size_t strlen(const char *);
void *memset(void *, int, size_t);
void *malloc(size_t);
void free(void *);
int atoi(const char *);

// I/O functions  
void printf(int fd, const char *, ...);  // Custom printf with file descriptor
char *gets(char *, int max);

// Special file descriptor numbers
#define STDIN  0
#define STDOUT 1  
#define STDERR 2