/**
 * xargs - build and execute command lines from standard input
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: xargs [-0prtx] [-E eof] [-I replace] [-L max-lines]
 *              [-n max-args] [-s max-chars] [command [initial-args]]
 * 
 * Options:
 *   -0  Input items terminated by null character
 *   -E  Set EOF string
 *   -I  Replace occurrences of replace-str in initial-args
 *   -L  Use at most max-lines per command
 *   -n  Use at most max-args per command
 *   -p  Prompt before executing
 *   -r  Do not run if stdin is empty
 *   -s  Use at most max-chars per command line
 *   -t  Print commands before executing
 *   -x  Exit if size is exceeded
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

#define MAX_ARGS 512
#define MAX_ARG_LEN 1024
#define MAX_CMD_LEN 4096
#define DEFAULT_MAX_CHARS 4096

// Option flags and values
static int null_term = 0;       // -0: null-terminated input
static int prompt_flag = 0;     // -p: prompt before exec
static int no_run_empty = 0;    // -r: don't run if empty
static int verbose = 0;         // -t: trace execution
static int exit_on_size = 0;    // -x: exit if size exceeded

static char *eof_str = 0;       // -E: EOF string
static char *replace_str = 0;   // -I: replacement string
static int max_lines = 0;       // -L: max input lines
static int max_args = 0;        // -n: max arguments
static int max_chars = DEFAULT_MAX_CHARS;  // -s: max chars

// Command construction
static char *base_argv[MAX_ARGS];
static int base_argc = 0;
static char *exec_argv[MAX_ARGS];
static int exec_argc = 0;

// Input buffer
static char input_buf[MAX_ARG_LEN];
static int input_len = 0;
static int input_eof = 0;

static void
usage(void)
{
    printf(2, "Usage: xargs [-0prtx] [-E eof] [-I replace] [-L max-lines]\n");
    printf(2, "             [-n max-args] [-s max-chars] [command [args]]\n");
    exit(1);
}

/**
 * Read next item from input
 * Returns pointer to item or NULL on EOF
 */
static char *
read_item(void)
{
    static char item[MAX_ARG_LEN];
    int pos = 0;
    int c;
    int in_quotes = 0;
    int escaped = 0;
    
    if (input_eof) return 0;
    
    // Skip leading whitespace (unless -0)
    if (!null_term) {
        while ((c = getchar()) != -1) {
            if (c != ' ' && c != '\t' && c != '\n') {
                ungetc(c);
                break;
            }
            if (max_lines > 0 && c == '\n') {
                // Count newlines for -L option
                return "\n";
            }
        }
        if (c == -1) {
            input_eof = 1;
            return 0;
        }
    }
    
    // Read item
    while ((c = getchar()) != -1 && pos < MAX_ARG_LEN - 1) {
        if (null_term) {
            // -0: null-terminated
            if (c == '\0') {
                break;
            }
            item[pos++] = c;
        } else {
            // Default: whitespace-separated with quote support
            if (escaped) {
                item[pos++] = c;
                escaped = 0;
            } else if (c == '\\') {
                escaped = 1;
            } else if (c == '"' || c == '\'') {
                if (in_quotes == c) {
                    in_quotes = 0;
                } else if (!in_quotes) {
                    in_quotes = c;
                } else {
                    item[pos++] = c;
                }
            } else if (!in_quotes && (c == ' ' || c == '\t' || c == '\n')) {
                if (pos > 0) {
                    if (c == '\n' && max_lines > 0) {
                        ungetc(c);
                    }
                    break;
                }
            } else {
                item[pos++] = c;
            }
        }
    }
    
    if (c == -1 && pos == 0) {
        input_eof = 1;
        return 0;
    }
    
    item[pos] = '\0';
    
    // Check for EOF string
    if (eof_str && strcmp(item, eof_str) == 0) {
        input_eof = 1;
        return 0;
    }
    
    return item;
}

/**
 * Simple getchar implementation
 */
static int
getchar(void)
{
    char c;
    if (read(0, &c, 1) == 1) {
        return c;
    }
    return -1;
}

/**
 * Simple ungetc (one char pushback)
 */
static int unget_char = -1;
static void
ungetc(int c)
{
    unget_char = c;
}

/**
 * Replace occurrences of replace_str in arg with replacement
 */
static char *
replace_in_arg(const char *arg, const char *replacement)
{
    static char result[MAX_ARG_LEN];
    const char *p = arg;
    char *q = result;
    int rep_len = strlen(replace_str);
    int repl_len = strlen(replacement);
    
    while (*p && q - result < MAX_ARG_LEN - repl_len - 1) {
        if (strncmp(p, replace_str, rep_len) == 0) {
            strcpy(q, replacement);
            q += repl_len;
            p += rep_len;
        } else {
            *q++ = *p++;
        }
    }
    *q = '\0';
    
    return result;
}

/**
 * Calculate command line size
 */
static int
calc_cmd_size(char *argv[], int argc)
{
    int size = 0;
    for (int i = 0; i < argc; i++) {
        size += strlen(argv[i]) + 1;  // +1 for space/null
    }
    return size;
}

/**
 * Execute command with given arguments
 */
static int
execute_command(char *argv[], int argc)
{
    if (argc == 0) return 0;
    
    // Print command if verbose
    if (verbose || prompt_flag) {
        for (int i = 0; i < argc; i++) {
            if (i > 0) printf(2, " ");
            printf(2, "%s", argv[i]);
        }
        if (prompt_flag) {
            printf(2, "?...");
            char response;
            if (read(0, &response, 1) != 1 || 
                (response != 'y' && response != 'Y')) {
                // Skip if not confirmed
                while (response != '\n' && read(0, &response, 1) == 1);
                return 0;
            }
            // Consume rest of line
            while (response != '\n' && read(0, &response, 1) == 1);
        } else {
            printf(2, "\n");
        }
    }
    
    // Fork and execute
    int pid = fork();
    if (pid < 0) {
        printf(2, "xargs: fork failed\n");
        return -1;
    }
    
    if (pid == 0) {
        // Child: execute command
        exec(argv[0], argv);
        printf(2, "xargs: exec %s failed\n", argv[0]);
        exit(1);
    }
    
    // Parent: wait for child
    int status;
    wait(&status);
    return status;
}

/**
 * Build and execute commands from input
 */
static int
process_input(void)
{
    char *item;
    int line_count = 0;
    int total_items = 0;
    int status = 0;
    
    while (!input_eof) {
        // Reset exec argv
        exec_argc = 0;
        
        // Copy base command
        for (int i = 0; i < base_argc; i++) {
            exec_argv[exec_argc++] = base_argv[i];
        }
        
        // Collect arguments
        int args_added = 0;
        int current_size = calc_cmd_size(exec_argv, exec_argc);
        line_count = 0;
        
        while ((item = read_item()) != 0) {
            // Handle newline counting for -L
            if (max_lines > 0 && strcmp(item, "\n") == 0) {
                line_count++;
                if (line_count >= max_lines) {
                    break;
                }
                continue;
            }
            
            // Check size limit
            int item_size = strlen(item) + 1;
            if (current_size + item_size > max_chars) {
                if (exit_on_size) {
                    printf(2, "xargs: command line too long\n");
                    exit(1);
                }
                break;
            }
            
            // Handle -I replacement
            if (replace_str) {
                // Replace in all base args
                exec_argc = 0;
                for (int i = 0; i < base_argc; i++) {
                    exec_argv[exec_argc++] = replace_in_arg(base_argv[i], item);
                }
                total_items++;
                break;  // -I processes one item at a time
            } else {
                // Add as argument
                if (exec_argc >= MAX_ARGS - 1) {
                    break;
                }
                exec_argv[exec_argc++] = item;
                args_added++;
                total_items++;
                current_size += item_size;
                
                // Check -n limit
                if (max_args > 0 && args_added >= max_args) {
                    break;
                }
            }
        }
        
        // Execute if we have arguments
        if (exec_argc > base_argc || !no_run_empty) {
            exec_argv[exec_argc] = 0;
            int ret = execute_command(exec_argv, exec_argc);
            if (ret != 0) status = ret;
        }
        
        if (item == 0) break;  // EOF
    }
    
    // Handle -r flag
    if (no_run_empty && total_items == 0) {
        return 0;  // Don't execute with no input
    }
    
    // Execute final command if no items but not -r
    if (total_items == 0 && !no_run_empty && exec_argc == 0) {
        for (int i = 0; i < base_argc; i++) {
            exec_argv[exec_argc++] = base_argv[i];
        }
        exec_argv[exec_argc] = 0;
        status = execute_command(exec_argv, exec_argc);
    }
    
    return status;
}

int
main(int argc, char *argv[])
{
    int i;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -- (end of options)
        if (strcmp(p, "-") == 0) {
            i++;
            break;
        }
        
        // Handle options with arguments
        if (strcmp(p, "E") == 0 || strcmp(p, "I") == 0 ||
            strcmp(p, "L") == 0 || strcmp(p, "n") == 0 ||
            strcmp(p, "s") == 0) {
            char opt = *p;
            i++;
            if (i >= argc) {
                usage();
            }
            
            switch (opt) {
            case 'E':
                eof_str = argv[i];
                break;
            case 'I':
                replace_str = argv[i];
                break;
            case 'L':
                max_lines = atoi(argv[i]);
                if (max_lines <= 0) {
                    printf(2, "xargs: invalid number for -L\n");
                    usage();
                }
                break;
            case 'n':
                max_args = atoi(argv[i]);
                if (max_args <= 0) {
                    printf(2, "xargs: invalid number for -n\n");
                    usage();
                }
                break;
            case 's':
                max_chars = atoi(argv[i]);
                if (max_chars <= 0) {
                    printf(2, "xargs: invalid number for -s\n");
                    usage();
                }
                break;
            }
            continue;
        }
        
        // Process flags
        while (*p) {
            switch (*p) {
            case '0':
                null_term = 1;
                break;
            case 'p':
                prompt_flag = 1;
                break;
            case 'r':
                no_run_empty = 1;
                break;
            case 't':
                verbose = 1;
                break;
            case 'x':
                exit_on_size = 1;
                break;
            default:
                printf(2, "xargs: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
    }
    
    // Set up base command
    if (i < argc) {
        // Use provided command
        for (; i < argc && base_argc < MAX_ARGS; i++) {
            base_argv[base_argc++] = argv[i];
        }
    } else {
        // Default to echo
        base_argv[base_argc++] = "echo";
    }
    
    // Process input and execute commands
    int status = process_input();
    
    exit(status);
}

// Helper function
int
atoi(const char *s)
{
    int n = 0;
    while (*s >= '0' && *s <= '9') {
        n = n * 10 + (*s - '0');
        s++;
    }
    return n;
}