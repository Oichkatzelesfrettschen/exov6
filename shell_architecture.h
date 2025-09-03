/*
 * POSIX-2024 Compliant Shell Architecture
 * MIT License - ExoKernel v6 Project
 * 
 * Comprehensive shell implementation based on:
 * - POSIX-2024 (IEEE 1003.1-2024) specification
 * - Toybox architecture principles
 * - Research into ash, dash, and other POSIX shells
 */

#pragma once

#include <types.h>

// =============================================================================
// POSIX-2024 SHELL COMMAND LANGUAGE PARSER
// =============================================================================

// Token types (based on POSIX shell grammar)
typedef enum {
    TOKEN_WORD,          // Regular words and literals
    TOKEN_ASSIGNMENT,    // Variable assignments (VAR=value)
    TOKEN_NAME,          // Variable names
    TOKEN_NEWLINE,       // Line terminators
    TOKEN_IO_NUMBER,     // File descriptor numbers (for redirection)
    
    // Operators
    TOKEN_AND_IF,        // &&
    TOKEN_OR_IF,         // ||
    TOKEN_DSEMI,         // ;;
    TOKEN_DLESS,         // <<
    TOKEN_DGREAT,        // >>
    TOKEN_LESSAND,       // <&
    TOKEN_GREATAND,      // >&
    TOKEN_LESSGREAT,     // <>
    TOKEN_DLESSDASH,     // <<-
    TOKEN_CLOBBER,       // >|
    
    // Single character tokens
    TOKEN_PIPE,          // |
    TOKEN_SEMI,          // ;
    TOKEN_AMP,           // &
    TOKEN_LESS,          // <
    TOKEN_GREAT,         // >
    TOKEN_LPAREN,        // (
    TOKEN_RPAREN,        // )
    TOKEN_LBRACE,        // {
    TOKEN_RBRACE,        // }
    
    // Reserved words
    TOKEN_IF,            // if
    TOKEN_THEN,          // then
    TOKEN_ELSE,          // else
    TOKEN_ELIF,          // elif
    TOKEN_FI,            // fi
    TOKEN_DO,            // do
    TOKEN_DONE,          // done
    TOKEN_CASE,          // case
    TOKEN_ESAC,          // esac
    TOKEN_WHILE,         // while
    TOKEN_UNTIL,         // until
    TOKEN_FOR,           // for
    TOKEN_FUNCTION,      // function
    TOKEN_IN,            // in
    TOKEN_BANG,          // !
    
    TOKEN_EOF,           // End of file
    TOKEN_ERROR          // Lexical errors
} token_type_t;

// Token structure
typedef struct token {
    token_type_t type;
    char *value;              // Token text
    int line;                 // Line number
    int column;               // Column position
    struct token *next;       // Next token in stream
} token_t;

// =============================================================================
// ABSTRACT SYNTAX TREE NODES
// =============================================================================

typedef enum {
    AST_SIMPLE_COMMAND,       // Simple commands
    AST_PIPELINE,             // Command pipelines
    AST_AND_OR_LIST,          // && and || chains
    AST_COMPOUND_COMMAND,     // { commands; }
    AST_SUBSHELL,            // ( commands )
    AST_IF_CLAUSE,           // if-then-else
    AST_WHILE_LOOP,          // while loops
    AST_FOR_LOOP,            // for loops
    AST_CASE_STATEMENT,      // case statements
    AST_FUNCTION_DEF,        // function definitions
    AST_REDIRECTION          // I/O redirections
} ast_node_type_t;

// Base AST node
typedef struct ast_node {
    ast_node_type_t type;
    int line;                 // Source line number
    struct ast_node *next;    // Next sibling node
} ast_node_t;

// Simple command node (command with arguments and redirections)
typedef struct {
    ast_node_t base;
    char **argv;              // Command arguments
    int argc;                 // Argument count
    struct redirection *redirections; // I/O redirections
    struct assignment *assignments;   // Variable assignments
} simple_command_t;

// Pipeline node (command1 | command2 | ...)
typedef struct {
    ast_node_t base;
    ast_node_t **commands;    // Array of commands
    int count;                // Number of commands in pipeline
    int background;           // True if pipeline should run in background
} pipeline_t;

// Redirection structure
typedef struct redirection {
    int fd;                   // File descriptor to redirect
    token_type_t type;        // Type of redirection (<, >, >>, etc.)
    char *target;             // Target file or file descriptor
    struct redirection *next; // Next redirection
} redirection_t;

// Variable assignment
typedef struct assignment {
    char *name;               // Variable name
    char *value;              // Variable value
    struct assignment *next;  // Next assignment
} assignment_t;

// =============================================================================
// SHELL STATE AND EXECUTION CONTEXT
// =============================================================================

// Shell options (set/unset commands)
typedef struct {
    unsigned int errexit:1;       // -e: exit on error
    unsigned int nounset:1;       // -u: error on undefined variables
    unsigned int verbose:1;       // -v: print input as read
    unsigned int xtrace:1;        // -x: trace execution
    unsigned int monitor:1;       // -m: job control
    unsigned int interactive:1;   // -i: interactive mode
    unsigned int login:1;         // -l: login shell
    unsigned int restricted:1;    // -r: restricted shell
    unsigned int posix:1;         // --posix: strict POSIX mode
    unsigned int noglob:1;        // -f: disable pathname expansion
    unsigned int noclobber:1;     // -C: don't overwrite files with >
} shell_options_t;

// Variable structure
typedef struct variable {
    char *name;
    char *value;
    unsigned int exported:1;      // Environment variable
    unsigned int readonly:1;      // Read-only variable
    struct variable *next;
} variable_t;

// Function definition
typedef struct function {
    char *name;
    ast_node_t *body;            // Function body AST
    struct function *next;
} function_t;

// Job structure (for job control)
typedef struct job {
    int id;                      // Job number
    pid_t pgid;                  // Process group ID
    pid_t *pids;                 // Array of process IDs
    int pid_count;               // Number of processes in job
    int status;                  // Job status
    char *command;               // Command line that started job
    struct job *next;
} job_t;

// Main shell context
typedef struct {
    // Parser state
    token_t *tokens;             // Token stream
    token_t *current_token;      // Current parsing position
    
    // Execution state
    shell_options_t options;     // Shell options
    variable_t *variables;       // Variable list
    function_t *functions;       // Function definitions
    job_t *jobs;                 // Job list
    
    // I/O state
    int stdin_fd;                // Standard input
    int stdout_fd;               // Standard output
    int stderr_fd;               // Standard error
    
    // Exit state
    int last_exit_status;        // Exit status of last command
    int exit_requested;          // Set when exit requested
    int exit_code;               // Exit code to use
    
    // Interactive features
    char *prompt1;               // Primary prompt (PS1)
    char *prompt2;               // Secondary prompt (PS2)
    int interactive;             // Interactive mode flag
    int job_control;             // Job control enabled
} shell_context_t;

// =============================================================================
// FUNCTION DECLARATIONS
// =============================================================================

// Lexer functions
token_t* tokenize(const char *input);
void free_tokens(token_t *tokens);
const char* token_type_name(token_type_t type);

// Parser functions
ast_node_t* parse_program(shell_context_t *ctx);
ast_node_t* parse_complete_commands(shell_context_t *ctx);
ast_node_t* parse_complete_command(shell_context_t *ctx);
ast_node_t* parse_list(shell_context_t *ctx);
ast_node_t* parse_and_or(shell_context_t *ctx);
ast_node_t* parse_pipeline(shell_context_t *ctx);
ast_node_t* parse_simple_command(shell_context_t *ctx);
void free_ast(ast_node_t *node);

// Executor functions
int execute_ast(shell_context_t *ctx, ast_node_t *node);
int execute_simple_command(shell_context_t *ctx, simple_command_t *cmd);
int execute_pipeline(shell_context_t *ctx, pipeline_t *pipeline);
int setup_redirections(redirection_t *redirections);

// Built-in commands
int builtin_cd(shell_context_t *ctx, char **argv);
int builtin_pwd(shell_context_t *ctx, char **argv);
int builtin_echo(shell_context_t *ctx, char **argv);
int builtin_test(shell_context_t *ctx, char **argv);
int builtin_set(shell_context_t *ctx, char **argv);
int builtin_unset(shell_context_t *ctx, char **argv);
int builtin_export(shell_context_t *ctx, char **argv);
int builtin_exit(shell_context_t *ctx, char **argv);
int builtin_return(shell_context_t *ctx, char **argv);
int builtin_shift(shell_context_t *ctx, char **argv);
int builtin_read(shell_context_t *ctx, char **argv);
int builtin_alias(shell_context_t *ctx, char **argv);
int builtin_unalias(shell_context_t *ctx, char **argv);
int builtin_jobs(shell_context_t *ctx, char **argv);
int builtin_fg(shell_context_t *ctx, char **argv);
int builtin_bg(shell_context_t *ctx, char **argv);
int builtin_type(shell_context_t *ctx, char **argv);
int builtin_command(shell_context_t *ctx, char **argv);
int builtin_eval(shell_context_t *ctx, char **argv);
int builtin_exec(shell_context_t *ctx, char **argv);
int builtin_trap(shell_context_t *ctx, char **argv);
int builtin_wait(shell_context_t *ctx, char **argv);
int builtin_times(shell_context_t *ctx, char **argv);
int builtin_umask(shell_context_t *ctx, char **argv);
int builtin_ulimit(shell_context_t *ctx, char **argv);

// Variable management
variable_t* get_variable(shell_context_t *ctx, const char *name);
char* get_variable_value(shell_context_t *ctx, const char *name);
void set_variable(shell_context_t *ctx, const char *name, const char *value);
void export_variable(shell_context_t *ctx, const char *name);
void unset_variable(shell_context_t *ctx, const char *name);

// Function management
function_t* get_function(shell_context_t *ctx, const char *name);
void define_function(shell_context_t *ctx, const char *name, ast_node_t *body);
void undefine_function(shell_context_t *ctx, const char *name);

// Job control
job_t* create_job(shell_context_t *ctx, const char *command);
void add_process_to_job(job_t *job, pid_t pid);
void wait_for_job(shell_context_t *ctx, job_t *job);
void update_job_status(shell_context_t *ctx);

// Shell initialization and cleanup
shell_context_t* init_shell(void);
void cleanup_shell(shell_context_t *ctx);
int run_shell(shell_context_t *ctx);

// Utility functions
char* expand_word(shell_context_t *ctx, const char *word);
int is_builtin(const char *name);
int word_split(const char *str, char ***words);
void free_word_list(char **words);

// Error handling
void shell_error(shell_context_t *ctx, const char *format, ...);
void syntax_error(shell_context_t *ctx, const char *message);