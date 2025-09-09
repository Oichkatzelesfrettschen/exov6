#include <types.h>
#include "user.h"
#include "fcntl.h"

// Working shell implementation - simplified but functional

#define MAXARGS 10
#define MAXLINE 100

// Parse command line into arguments
int parse_cmd(char *buf, char *argv[]) {
    int argc = 0;
    char *p = buf;
    
    // Skip leading whitespace
    while (*p == ' ' || *p == '\t') p++;
    
    while (*p && argc < MAXARGS - 1) {
        argv[argc++] = p;
        
        // Find end of argument
        while (*p && *p != ' ' && *p != '\t' && *p != '\n') p++;
        
        if (*p) {
            *p++ = '\0';  // Null-terminate argument
            // Skip whitespace
            while (*p == ' ' || *p == '\t') p++;
        }
    }
    
    argv[argc] = 0;  // Null-terminate argv
    return argc;
}

// Built-in commands
int builtin_cd(char *argv[]) {
    if (argv[1] == 0) {
        // cd with no arguments - go to root
        if (chdir("/") < 0) {
            printf(2, "cd: cannot change to /\n");
        }
    } else {
        if (chdir(argv[1]) < 0) {
            printf(2, "cd: cannot change to %s\n", argv[1]);
        }
    }
    return 1;  // Built-in handled
}

int builtin_exit(char *argv[]) {
    (void)argv;  // Unused
    printf(1, "Shell exiting...\n");
    exit(0);
}

// Check if command is a built-in
int handle_builtin(char *argv[]) {
    if (argv[0] == 0) return 1;  // Empty command
    
    if (strcmp(argv[0], "cd") == 0) {
        return builtin_cd(argv);
    }
    
    if (strcmp(argv[0], "exit") == 0) {
        return builtin_exit(argv);
    }
    
    return 0;  // Not a built-in
}

// Execute external command
void exec_cmd(char *argv[]) {
    int pid;
    
    pid = fork();
    if (pid == 0) {
        // Child process
        if (exec(argv[0], argv) < 0) {
            printf(2, "sh: %s: command not found\n", argv[0]);
            exit(0);
        }
    } else if (pid > 0) {
        // Parent process - wait for child
        wait();
    } else {
        printf(2, "sh: fork failed\n");
    }
}

// Get command line input
int getcmd(char *buf, int nbuf) {
    printf(1, "$ ");  // Shell prompt
    memset(buf, 0, nbuf);
    gets(buf, nbuf);
    
    if (buf[0] == 0) {  // EOF
        return -1;
    }
    
    return 0;
}

int main(void) {
    static char buf[MAXLINE];
    static char *argv[MAXARGS];
    int argc;
    
    printf(1, "ExoKernel v6 Shell\n");
    printf(1, "Type 'exit' to quit\n\n");
    
    // Main shell loop
    while (getcmd(buf, sizeof(buf)) >= 0) {
        // Parse command
        argc = parse_cmd(buf, argv);
        
        if (argc == 0) continue;  // Empty command
        
        // Handle built-in commands
        if (handle_builtin(argv)) {
            continue;
        }
        
        // Execute external command
        exec_cmd(argv);
    }
    
    printf(1, "Shell terminated\n");
    exit(0);
}