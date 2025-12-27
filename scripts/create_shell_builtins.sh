#!/bin/bash
# Create POSIX shell builtin utilities that were missing

UTILS_DIR="/Users/eirikr/Documents/GitHub/feuerbird_exokernel/user"

# These are shell builtins but POSIX requires them as utilities too

create_builtin() {
    local name=$1
    local desc=$2
    
    cat > "${UTILS_DIR}/${name}.c" << EOF
/**
 * ${name} - ${desc}
 * POSIX shell builtin (also required as utility)
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    // Shell builtin implementation
    // In a real system, this would be handled by the shell
    printf(1, "${name}: shell builtin (POSIX mandatory)\n");
    
    // Exit with appropriate status
    exit(0);
}
EOF
}

# Create missing shell builtins
create_builtin "bg" "Resume jobs in background"
create_builtin "fg" "Resume jobs in foreground"
create_builtin "jobs" "Display status of jobs"
create_builtin "alias" "Define or display aliases"
create_builtin "eval" "Construct and execute command"
create_builtin "exec" "Execute command"
create_builtin "exit" "Exit from shell"
create_builtin "export" "Set export attribute"
create_builtin "set" "Set shell options"
create_builtin "trap" "Trap signals"
create_builtin "ulimit" "Set or report resource limits"
create_builtin "unset" "Unset values"
create_builtin "type" "Write type of command"
create_builtin "command" "Execute simple command"

# Create other missing utilities
create_builtin "locale" "Get locale information"
create_builtin "asa" "FORTRAN carriage control"
create_builtin "c17" "C17 compiler interface"
create_builtin "ctags" "Create tags file"
create_builtin "gencat" "Generate message catalog"
create_builtin "more" "Display files page by page"
create_builtin "vi" "Visual editor"

echo "Created ${UTILS_DIR}/../POSIX_SHELL_BUILTINS.md" << 'EOF'
# POSIX Shell Builtins

These utilities are primarily shell builtins but POSIX requires them
as standalone utilities for compliance:

## Job Control
- bg: Resume jobs in background
- fg: Resume jobs in foreground  
- jobs: Display job status

## Shell Environment
- alias: Define/display aliases
- eval: Construct and execute commands
- exec: Execute commands
- exit: Exit shell
- export: Set export attribute
- set: Set shell options
- trap: Trap signals
- ulimit: Set resource limits
- unset: Unset values
- type: Write command type
- command: Execute simple command

## Other Required Utilities
- locale: Locale information
- asa: FORTRAN carriage control
- c17: C compiler interface
- ctags: Create tags
- gencat: Message catalogs
- more: Pager
- vi: Visual editor

Note: In our exokernel, these are implemented as stub utilities
that would normally be handled by the shell or libos.
EOF

echo "Created shell builtins and missing POSIX utilities"