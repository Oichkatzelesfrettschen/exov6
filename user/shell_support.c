/*
 * Shell Support Functions - Helper implementations
 * MIT License - ExoKernel v6 Project
 */

#include <types.h>
#include "user_minimal.h"
#include "shell_architecture.h"

// =============================================================================
// VARIABLE MANAGEMENT
// =============================================================================

variable_t* get_variable(shell_context_t *ctx, const char *name) {
    variable_t *var = ctx->variables;
    while (var) {
        if (strcmp(var->name, name) == 0) {
            return var;
        }
        var = var->next;
    }
    return NULL;
}

char* get_variable_value(shell_context_t *ctx, const char *name) {
    variable_t *var = get_variable(ctx, name);
    return var ? var->value : NULL;
}

void set_variable(shell_context_t *ctx, const char *name, const char *value) {
    variable_t *var = get_variable(ctx, name);
    
    if (var) {
        // Update existing variable
        if (var->readonly) {
            shell_error(ctx, "%s: readonly variable", name);
            return;
        }
        free(var->value);
        var->value = malloc(strlen(value) + 1);
        strcpy(var->value, value);
    } else {
        // Create new variable
        var = malloc(sizeof(variable_t));
        if (!var) return;
        
        var->name = malloc(strlen(name) + 1);
        strcpy(var->name, name);
        var->value = malloc(strlen(value) + 1);
        strcpy(var->value, value);
        var->exported = 0;
        var->readonly = 0;
        
        // Add to list
        var->next = ctx->variables;
        ctx->variables = var;
    }
}

void export_variable(shell_context_t *ctx, const char *name) {
    variable_t *var = get_variable(ctx, name);
    if (var) {
        var->exported = 1;
    }
}

void unset_variable(shell_context_t *ctx, const char *name) {
    variable_t **var_ptr = &ctx->variables;
    
    while (*var_ptr) {
        variable_t *var = *var_ptr;
        if (strcmp(var->name, name) == 0) {
            if (var->readonly) {
                shell_error(ctx, "%s: readonly variable", name);
                return;
            }
            
            // Remove from list
            *var_ptr = var->next;
            
            // Free memory
            free(var->name);
            free(var->value);
            free(var);
            return;
        }
        var_ptr = &var->next;
    }
}

// =============================================================================
// ADDITIONAL BUILT-IN COMMANDS
// =============================================================================

int builtin_set(shell_context_t *ctx, char **argv) {
    // Simplified set implementation
    if (!argv[1]) {
        // Print all variables
        variable_t *var = ctx->variables;
        while (var) {
            printf(STDOUT, "%s=%s\n", var->name, var->value);
            var = var->next;
        }
        return 0;
    }
    
    // Handle options (simplified)
    for (int i = 1; argv[i]; i++) {
        if (strcmp(argv[i], "-e") == 0) {
            ctx->options.errexit = 1;
        } else if (strcmp(argv[i], "+e") == 0) {
            ctx->options.errexit = 0;
        } else if (strcmp(argv[i], "-x") == 0) {
            ctx->options.xtrace = 1;
        } else if (strcmp(argv[i], "+x") == 0) {
            ctx->options.xtrace = 0;
        }
        // Add more options as needed
    }
    
    return 0;
}

int builtin_unset(shell_context_t *ctx, char **argv) {
    if (!argv[1]) {
        shell_error(ctx, "unset: missing operand");
        return 1;
    }
    
    for (int i = 1; argv[i]; i++) {
        unset_variable(ctx, argv[i]);
    }
    
    return 0;
}

int builtin_export(shell_context_t *ctx, char **argv) {
    if (!argv[1]) {
        // Print exported variables
        variable_t *var = ctx->variables;
        while (var) {
            if (var->exported) {
                printf(STDOUT, "export %s=%s\n", var->name, var->value);
            }
            var = var->next;
        }
        return 0;
    }
    
    for (int i = 1; argv[i]; i++) {
        char *name = argv[i];
        char *value = strchr(name, '=');
        
        if (value) {
            // export VAR=value
            *value = '\0';
            value++;
            set_variable(ctx, name, value);
            export_variable(ctx, name);
        } else {
            // export VAR (mark existing variable for export)
            export_variable(ctx, name);
        }
    }
    
    return 0;
}

int builtin_return(shell_context_t *ctx, char **argv) {
    // Simplified return implementation
    int code = ctx->last_exit_status;
    if (argv[1]) {
        code = atoi(argv[1]);
    }
    return code;
}

int builtin_shift(shell_context_t *ctx, char **argv) {
    // Simplified shift implementation
    // In a full shell, this would shift positional parameters
    return 0;
}

int builtin_read(shell_context_t *ctx, char **argv) {
    if (!argv[1]) {
        shell_error(ctx, "read: missing variable name");
        return 1;
    }
    
    char input[256];
    if (gets(input, sizeof(input))) {
        set_variable(ctx, argv[1], input);
        return 0;
    }
    
    return 1;
}

int builtin_alias(shell_context_t *ctx, char **argv) {
    // Simplified alias implementation
    // In a full shell, this would manage command aliases
    return 0;
}

int builtin_unalias(shell_context_t *ctx, char **argv) {
    // Simplified unalias implementation
    return 0;
}

int builtin_jobs(shell_context_t *ctx, char **argv) {
    // Simplified jobs implementation
    printf(STDOUT, "No active jobs\n");
    return 0;
}

int builtin_fg(shell_context_t *ctx, char **argv) {
    // Simplified fg implementation
    return 0;
}

int builtin_bg(shell_context_t *ctx, char **argv) {
    // Simplified bg implementation
    return 0;
}

int builtin_type(shell_context_t *ctx, char **argv) {
    if (!argv[1]) {
        shell_error(ctx, "type: missing operand");
        return 1;
    }
    
    // Check if it's a built-in
    for (int i = 0; builtin_commands[i].name; i++) {
        if (strcmp(argv[1], builtin_commands[i].name) == 0) {
            printf(STDOUT, "%s is a shell builtin\n", argv[1]);
            return 0;
        }
    }
    
    // Check if it's an external command
    printf(STDOUT, "%s is %s\n", argv[1], argv[1]);
    return 0;
}

int builtin_command(shell_context_t *ctx, char **argv) {
    // Simplified command implementation
    if (argv[1]) {
        // Execute the command, bypassing functions and aliases
        return execute_simple_command(ctx, (simple_command_t*)argv);
    }
    return 0;
}

int builtin_eval(shell_context_t *ctx, char **argv) {
    // Simplified eval implementation
    // In a full shell, this would parse and execute the arguments as commands
    return 0;
}

int builtin_exec(shell_context_t *ctx, char **argv) {
    if (!argv[1]) {
        return 0;
    }
    
    // Replace shell with the specified command
    exec(argv[1], argv + 1);
    shell_error(ctx, "exec: %s: command not found", argv[1]);
    return 127;
}

int builtin_trap(shell_context_t *ctx, char **argv) {
    // Simplified trap implementation
    return 0;
}

int builtin_wait(shell_context_t *ctx, char **argv) {
    // Simplified wait implementation
    wait(NULL);
    return 0;
}

int builtin_times(shell_context_t *ctx, char **argv) {
    // Simplified times implementation
    printf(STDOUT, "0m0.000s 0m0.000s\n0m0.000s 0m0.000s\n");
    return 0;
}

int builtin_umask(shell_context_t *ctx, char **argv) {
    // Simplified umask implementation
    if (!argv[1]) {
        printf(STDOUT, "022\n");
    }
    return 0;
}

int builtin_ulimit(shell_context_t *ctx, char **argv) {
    // Simplified ulimit implementation
    return 0;
}

// =============================================================================
// UTILITY FUNCTIONS
// =============================================================================

void shell_error(shell_context_t *ctx, const char *format, ...) {
    // Simplified error reporting
    printf(STDERR, "shell: error: %s\n", format);
}

void syntax_error(shell_context_t *ctx, const char *message) {
    printf(STDERR, "shell: syntax error: %s\n", message);
}

int setup_redirections(redirection_t *redirections) {
    // Simplified redirection setup
    // In a full shell, this would handle <, >, >>, |, etc.
    return 0;
}

void free_tokens(token_t *tokens) {
    while (tokens) {
        token_t *next = tokens->next;
        free(tokens->value);
        free(tokens);
        tokens = next;
    }
}

void cleanup_shell(shell_context_t *ctx) {
    if (!ctx) return;
    
    // Free variables
    variable_t *var = ctx->variables;
    while (var) {
        variable_t *next = var->next;
        free(var->name);
        free(var->value);
        free(var);
        var = next;
    }
    
    // Free functions
    function_t *func = ctx->functions;
    while (func) {
        function_t *next = func->next;
        free(func->name);
        free_ast(func->body);
        free(func);
        func = next;
    }
    
    // Free jobs
    job_t *job = ctx->jobs;
    while (job) {
        job_t *next = job->next;
        free(job->command);
        free(job->pids);
        free(job);
        job = next;
    }
    
    free(ctx);
}

void free_ast(ast_node_t *node) {
    // Simplified AST cleanup
    if (node) {
        free(node);
    }
}

// Simple string utility functions
int atoi(const char *str) {
    int result = 0;
    int sign = 1;
    
    if (*str == '-') {
        sign = -1;
        str++;
    } else if (*str == '+') {
        str++;
    }
    
    while (*str >= '0' && *str <= '9') {
        result = result * 10 + (*str - '0');
        str++;
    }
    
    return sign * result;
}

char* strncpy(char *dest, const char *src, int n) {
    int i;
    for (i = 0; i < n && src[i]; i++) {
        dest[i] = src[i];
    }
    while (i < n) {
        dest[i++] = '\0';
    }
    return dest;
}

char* strcpy(char *dest, const char *src) {
    int i = 0;
    while (src[i]) {
        dest[i] = src[i];
        i++;
    }
    dest[i] = '\0';
    return dest;
}

char* strchr(const char *s, char c) {
    while (*s) {
        if (*s == c) {
            return (char*)s;
        }
        s++;
    }
    return (*s == c) ? (char*)s : NULL;
}