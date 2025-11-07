/*
 * mksh - MirBSD Korn Shell (simplified implementation for ExoV6)
 * 
 * A POSIX-compliant shell with ksh93 features, optimized for exokernel.
 * This is a lightweight implementation suitable for embedded/minimal systems.
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

#define MAXARGS 16
#define MAXLINE 512
#define MAXPATH 256

/* Shell state */
static char cwd[MAXPATH];
static int last_exit_status = 0;

/* Builtin commands */
static int cmd_cd(int argc, char **argv);
static int cmd_exit(int argc, char **argv);
static int cmd_export(int argc, char **argv);
static int cmd_pwd(int argc, char **argv);
static int cmd_echo(int argc, char **argv);

struct builtin {
    const char *name;
    int (*func)(int argc, char **argv);
};

static struct builtin builtins[] = {
    {"cd", cmd_cd},
    {"exit", cmd_exit},
    {"export", cmd_export},
    {"pwd", cmd_pwd},
    {"echo", cmd_echo},
    {0, 0}
};

/* Execute a command */
static int execute_cmd(int argc, char **argv) {
    int i;
    
    if (argc == 0)
        return 0;
    
    /* Check for builtins */
    for (i = 0; builtins[i].name; i++) {
        if (strcmp(argv[0], builtins[i].name) == 0) {
            return builtins[i].func(argc, argv);
        }
    }
    
    /* External command */
    int pid = fork();
    if (pid == 0) {
        /* Child process */
        exec(argv[0], argv);
        printf(2, "mksh: %s: command not found\n", argv[0]);
        exit(1);
    } else if (pid > 0) {
        /* Parent process */
        int status;
        wait(&status);
        return status;
    } else {
        printf(2, "mksh: fork failed\n");
        return -1;
    }
}

/* Parse and execute a command line */
static int parse_and_execute(char *line) {
    char *argv[MAXARGS];
    int argc = 0;
    char *p = line;
    
    /* Simple tokenization (whitespace-separated) */
    while (*p && argc < MAXARGS - 1) {
        /* Skip whitespace */
        while (*p == ' ' || *p == '\t')
            p++;
        
        if (*p == '\0')
            break;
        
        argv[argc++] = p;
        
        /* Find end of token */
        while (*p && *p != ' ' && *p != '\t' && *p != '\n')
            p++;
        
        if (*p)
            *p++ = '\0';
    }
    argv[argc] = 0;
    
    return execute_cmd(argc, argv);
}

/* Builtin: cd */
static int cmd_cd(int argc, char **argv) {
    (void)argc;
    const char *dir = argv[1] ? argv[1] : "/";
    
    if (chdir(dir) < 0) {
        printf(2, "mksh: cd: %s: no such directory\n", dir);
        return 1;
    }
    
    return 0;
}

/* Builtin: exit */
static int cmd_exit(int argc, char **argv) {
    int code = 0;
    if (argc > 1)
        code = atoi(argv[1]);
    exit(code);
    return 0; /* Never reached */
}

/* Builtin: export (simplified) */
static int cmd_export(int argc, char **argv) {
    (void)argc;
    (void)argv;
    /* Environment variables not fully implemented yet */
    printf(2, "mksh: export: not yet implemented\n");
    return 0;
}

/* Builtin: pwd */
static int cmd_pwd(int argc, char **argv) {
    (void)argc;
    (void)argv;
    
    if (getcwd(cwd, sizeof(cwd)) == 0) {
        printf(2, "mksh: pwd: getcwd failed\n");
        return 1;
    }
    
    printf(1, "%s\n", cwd);
    return 0;
}

/* Builtin: echo */
static int cmd_echo(int argc, char **argv) {
    int i;
    for (i = 1; i < argc; i++) {
        printf(1, "%s", argv[i]);
        if (i < argc - 1)
            printf(1, " ");
    }
    printf(1, "\n");
    return 0;
}

/* Print prompt */
static void print_prompt(void) {
    if (getcwd(cwd, sizeof(cwd)) != 0) {
        printf(1, "mksh:%s$ ", cwd);
    } else {
        printf(1, "mksh$ ");
    }
}

/* Main shell loop */
int main(int argc, char *argv[]) {
    char line[MAXLINE];
    int n;
    
    (void)argc;
    (void)argv;
    
    /* Initialize */
    getcwd(cwd, sizeof(cwd));
    
    /* Interactive mode */
    while (1) {
        print_prompt();
        
        /* Read command */
        memset(line, 0, sizeof(line));
        n = 0;
        while (n < MAXLINE - 1) {
            int c;
            if (read(0, &c, 1) != 1)
                exit(0);
            
            if (c == '\n')
                break;
            
            line[n++] = c;
        }
        line[n] = '\0';
        
        if (n == 0)
            continue;
        
        /* Execute */
        last_exit_status = parse_and_execute(line);
    }
    
    return 0;
}
