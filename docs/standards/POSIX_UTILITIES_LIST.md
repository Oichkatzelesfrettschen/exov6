# POSIX.1-2024 (SUSv5) Required Utilities

## Core POSIX Utilities Required for Compliance

Based on the POSIX.1-2024 (SUSv5) specification, the following utilities are required for a conforming POSIX system. This list is organized by category for implementation priority.

### Shell and Control Flow Utilities
- [x] sh - POSIX shell (implemented in user/sh.c)
- [x] echo - write arguments to stdout (implemented in user/echo.c) 
- [ ] true - return true value
- [ ] false - return false value
- [ ] test - evaluate conditional expression
- [ ] [ - evaluate conditional expression (alias for test)
- [ ] sleep - suspend execution for an interval
- [ ] wait - await process completion
- [ ] exit - cause shell to exit
- [ ] return - return from function
- [ ] break - exit from loop
- [ ] continue - continue loop
- [ ] eval - construct and execute command
- [ ] exec - execute commands
- [ ] export - set export attribute for variables
- [ ] readonly - set readonly attribute for variables
- [ ] set - set shell options and positional parameters
- [ ] shift - shift positional parameters
- [ ] trap - trap signals
- [ ] unset - unset values and attributes
- [ ] . (dot) - execute commands in current environment
- [ ] : (colon) - null utility

### File and Directory Operations
- [x] cat - concatenate and print files (implemented in user/cat.c)
- [x] ls - list directory contents (implemented in user/ls.c)
- [x] mkdir - make directories (implemented in user/mkdir.c)
- [x] rm - remove files (implemented in user/rm.c)
- [x] ln - link files (implemented in user/ln.c)
- [ ] cp - copy files
- [ ] mv - move files
- [ ] rmdir - remove directories
- [ ] pwd - print working directory
- [ ] cd - change directory
- [ ] chmod - change file modes
- [ ] chown - change file ownership
- [ ] touch - change file access and modification times
- [ ] find - find files
- [ ] du - estimate file space usage
- [ ] df - report file system disk space usage
- [ ] basename - return filename portion of pathname
- [ ] dirname - return directory portion of pathname
- [ ] pathchk - check pathname validity
- [ ] mkfifo - make FIFO special files
- [ ] mknod - make special files

### Text Processing Utilities
- [x] grep - search text patterns (implemented in user/grep.c)
- [x] wc - word, line, character, and byte count (implemented in user/wc.c)
- [ ] sed - stream editor
- [ ] awk - pattern scanning and processing language
- [ ] cut - cut out selected fields
- [ ] paste - merge lines of files
- [ ] sort - sort lines of text files
- [ ] uniq - report or filter unique lines
- [ ] tr - translate characters
- [ ] head - output first part of files
- [ ] tail - output last part of files
- [ ] tee - duplicate standard input
- [ ] comm - compare sorted files
- [ ] diff - compare files line by line
- [ ] cmp - compare two files
- [ ] od - dump files in various formats
- [ ] fold - filter for folding lines
- [ ] join - relational database operator
- [ ] split - split files into pieces
- [ ] csplit - split files based on context
- [ ] expand - convert tabs to spaces
- [ ] unexpand - convert spaces to tabs
- [ ] pr - print files
- [ ] nl - line numbering filter
- [ ] fmt - simple text formatter

### Process Management
- [x] kill - terminate or signal processes (implemented in user/kill.c)
- [x] init - process control initialization (implemented in user/init.c)
- [ ] ps - report process status
- [ ] jobs - display status of jobs
- [ ] fg - run jobs in foreground
- [ ] bg - run jobs in background
- [ ] nice - run with modified priority
- [ ] nohup - run immune to hangups
- [ ] time - time a simple command
- [ ] times - write process times

### System Administration
- [ ] date - write date and time
- [ ] cal - print calendar
- [ ] who - show who is logged on
- [ ] id - return user identity
- [ ] uname - return system name
- [ ] hostname - display hostname
- [ ] logname - return login name
- [ ] tty - return terminal name
- [ ] stty - set terminal characteristics
- [ ] env - set environment for command invocation
- [ ] getconf - get configuration values
- [ ] locale - get locale information
- [ ] localedef - define locale environment

### Development Utilities
- [ ] make - maintain program dependencies
- [ ] cc/c99 - C compiler
- [ ] lex - lexical analyzer generator
- [ ] yacc - yet another compiler compiler
- [ ] ar - create and maintain library archives
- [ ] nm - write symbol table
- [ ] strip - remove unnecessary information from executables
- [ ] ctags - create tags file
- [ ] cflow - generate C flow graph
- [ ] cxref - generate C cross-reference

### Archive and Compression
- [ ] tar - file archiver
- [ ] cpio - copy file archives
- [ ] pax - portable archive interchange
- [ ] compress - compress data
- [ ] uncompress - expand compressed data
- [ ] zcat - expand and concatenate data

### Communication Utilities
- [ ] mailx - send and receive mail
- [ ] write - send message to another user
- [ ] mesg - permit or deny messages
- [ ] talk - talk to another user
- [ ] logger - log messages
- [ ] syslog - log system messages

### Mathematical Utilities
- [ ] bc - arbitrary precision arithmetic language
- [ ] dc - desk calculator
- [ ] expr - evaluate expressions
- [ ] factor - factor numbers

### Miscellaneous Utilities
- [x] printf - write formatted output (implemented in user/printf.c)
- [ ] read - read a line from standard input
- [ ] alias - define or display aliases
- [ ] unalias - remove alias definitions
- [ ] hash - remember or display program locations
- [ ] type - write type of command
- [ ] command - execute simple command
- [ ] getopt - parse utility options
- [ ] getopts - parse utility options
- [ ] xargs - construct argument lists
- [ ] at - execute commands at a later time
- [ ] batch - schedule commands for batch execution
- [ ] crontab - schedule periodic background work

## Implementation Status

### Currently Implemented (13/150+)
- Basic shell (sh)
- File operations: cat, ls, mkdir, rm, ln
- Text processing: grep, wc
- Process management: init, kill
- Output: echo, printf
- Testing: forktest, stressfs, usertests

### Priority 1: Essential Missing Utilities (20)
These are critical for basic POSIX compliance:
- cp, mv, pwd, cd, chmod
- ps, test, true, false, sleep
- head, tail, sed (basic)
- env, date, uname
- touch, find (basic)

### Priority 2: Important Utilities (30)
These provide important functionality:
- awk, sort, uniq, tr, cut, paste
- diff, cmp, comm
- tar, compress
- make, cc/c99
- who, id, tty

### Priority 3: Full Compliance (100+)
Remaining utilities for complete POSIX.1-2024 compliance.

## Implementation Notes

1. **Exokernel Considerations**: 
   - Utilities should be implemented using libos system calls
   - File operations go through capability-based access control
   - Process management uses exokernel IPC mechanisms

2. **Code Organization**:
   - Each utility in separate .c file in user/ directory
   - Shared functionality in user/ulib.c
   - POSIX-compliant interfaces in libos/

3. **Testing Requirements**:
   - Each utility needs comprehensive test in tests/
   - POSIX compliance tests in tests/posix_compliance/
   - Integration tests with shell scripts

4. **Documentation**:
   - Man page equivalent in docs/utilities/
   - Usage examples in each source file
   - Compliance notes for deviations from POSIX