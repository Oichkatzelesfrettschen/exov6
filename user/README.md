# ExoV6 Userland - Modern Organization

This directory contains the complete POSIX userland for ExoV6, organized into logical categories for maintainability and modularity.

## Directory Structure

```
user/
├── CMakeLists.txt           # Modern auto-discovery build system
├── README.md                # This file
├── [libraries]              # Core user-space libraries
│   ├── ulib.c              # User library (syscall wrappers)
│   ├── umalloc.c           # User-space malloc
│   ├── printf.c            # Printf implementation
│   ├── caplib.c            # Capability library
│   ├── chan.c              # Channel IPC library
│   ├── door.c              # Door IPC library
│   └── math_core.c         # Math utilities
└── [programs]              # User programs (215+)
```

## Program Categories

### Core Utilities (12 programs)
File operations and basic system commands:
- `cat` - Concatenate files
- `cp` - Copy files
- `mv` - Move files
- `rm` - Remove files
- `ls` - List directory
- `mkdir` - Make directory
- `ln` - Create links
- `touch` - Update timestamps
- `pwd` - Print working directory
- `chmod` - Change permissions
- `chown` - Change owner
- `chgrp` - Change group

**Build:** `make userland-core`

### Text Processing (12 programs)
Text manipulation and analysis:
- `grep` - Search text patterns
- `sed` - Stream editor
- `awk` - Pattern scanning
- `cut` - Cut out sections
- `tr` - Translate characters
- `sort` - Sort lines
- `uniq` - Filter unique lines
- `wc` - Word count
- `head` - Output first lines
- `tail` - Output last lines
- `diff` - Compare files
- `patch` - Apply diff patches

**Build:** `make userland-text`

### Archive Tools (7 programs)
Compression and archiving:
- `tar` - Tape archive
- `gzip` - GNU zip
- `bzip2` - Bzip2 compression
- `zip` - PKZip format
- `unzip` - Extract zip files
- `compress` - Unix compress
- `ar` - Archive utility

**Build:** `make userland-archive`

### Shell Tools (7 programs)
Command shells and utilities:
- `sh` - POSIX shell
- `mksh` - MirBSD Korn Shell
- `echo` - Echo arguments
- `env` - Environment display
- `export` - Export variables
- `alias` - Command aliases
- `command` - Execute commands

**Build:** `make userland-shell`

### System Utilities (7 programs)
System management:
- `ps` - Process status
- `kill` - Send signals
- `top` - Process monitor
- `df` - Disk free
- `du` - Disk usage
- `mount` - Mount filesystems
- `init` - Init process

**Build:** `make userland-system`

### Network Tools (6 programs)
Network utilities:
- `ping` - ICMP echo
- `netstat` - Network statistics
- `ifconfig` - Interface configuration
- `route` - Routing table
- `curl` - Transfer data (planned)
- `wget` - Download files (planned)

**Build:** `make userland-network`

### Development Tools (8 programs)
Compiler and development:
- `cc` - C compiler wrapper
- `gcc` - GNU C compiler
- `make` - Build automation
- `cmake` - Modern build system
- `gdb` - GNU debugger
- `nm` - Symbol lister
- `objdump` - Object dump
- `strip` - Strip symbols

**Build:** `make userland-dev`

### Test Programs (4 programs)
System testing:
- `usertests` - User-space tests
- `forktest` - Fork testing
- `stressfs` - Filesystem stress
- `zombie` - Zombie process test

**Build:** `make userland-test`

## Build System Features

### Auto-Discovery
The modern build system automatically discovers and builds all programs:
```cmake
# Programs are organized by category
set(CORE_UTILS cat cp mv rm ls mkdir ln touch pwd chmod chown chgrp)
set(TEXT_PROCESSING grep sed awk cut tr sort uniq wc head tail diff patch)
# ... etc
```

### Category-Based Building
Build specific categories:
```bash
cmake --build . --target userland-core      # Just core utilities
cmake --build . --target userland-text      # Just text processing
cmake --build . --target userland-all       # Everything
```

### Standard Dependencies
All programs automatically link against:
- `phoenix-ulib` - System call wrappers
- `phoenix-umalloc` - User-space allocator
- `phoenix-printf` - Printf implementation
- `phoenix-caplib` - Capability library

### Special Programs
Some programs have extra dependencies:
```cmake
fileserver -> phoenix-chan, phoenix-door  # IPC libraries
```

## Adding New Programs

1. Create `newprog.c` in this directory
2. Add to appropriate category in CMakeLists.txt:
   ```cmake
   set(CORE_UTILS
       cat cp mv rm ... newprog  # Add here
   )
   ```
3. Rebuild: `cmake --build .`

The program will automatically:
- Link against standard dependencies
- Get proper output name
- Be included in category target

## Library Organization

### Core Libraries
- **ulib.c**: Syscall wrappers (fork, exec, wait, open, read, write, etc.)
- **umalloc.c**: Malloc implementation using sbrk
- **printf.c**: Printf/sprintf/fprintf family

### IPC Libraries
- **caplib.c**: Capability management (create, transfer, revoke)
- **chan.c**: Channel-based IPC (message passing)
- **door.c**: Door-based IPC (RPC mechanism)

### Utility Libraries
- **math_core.c**: Math functions (sqrt, sin, cos, etc.)

## Program Status

| Category | Total | Implemented | Stubbed | Planned |
|----------|-------|-------------|---------|---------|
| Core Utils | 12 | 12 | 0 | 0 |
| Text Processing | 12 | 12 | 0 | 0 |
| Archive | 7 | 7 | 0 | 0 |
| Shell | 7 | 7 | 0 | 0 |
| System | 7 | 7 | 0 | 0 |
| Network | 6 | 4 | 2 | 0 |
| Development | 8 | 8 | 0 | 0 |
| Test | 4 | 4 | 0 | 0 |
| **Total** | **63** | **61** | **2** | **0** |

## Modularization Strategy

### Shared Code Patterns
Common functionality extracted to libraries:
- File I/O → ulib.c
- Memory management → umalloc.c
- String formatting → printf.c
- Capability operations → caplib.c

### Code Reuse
Programs use library functions instead of duplicating:
```c
// Old: inline implementation
void *my_malloc(size_t size) { /* implementation */ }

// New: library call
void *my_malloc(size_t size) {
    return malloc(size);  // From umalloc library
}
```

### Minimal Duplication
Each program focuses on its core functionality, delegating common operations to libraries.

## Integration with ExoV6

### Capability Integration
All programs use exokernel capabilities:
```c
#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(void) {
    // Capabilities automatically managed by ulib
    int fd = open("/file", O_RDONLY);  // Gets file capability
    // ...
}
```

### LibOS Layer
Programs can optionally use LibOS services for higher-level abstractions:
```c
#include "posix.h"  // POSIX LibOS

// POSIX-compatible operations with LibOS policy
```

## Documentation

- **DOCUMENTATION.md**: Complete system documentation
- **kernel/resurrection/README.md**: Process resurrection
- **doc/posix_compat.md**: POSIX compatibility matrix

## Testing

Run all tests:
```bash
cmake --build . --target userland-test
./usertests
./forktest
./stressfs
```

## Performance

Programs are optimized for:
- **Minimal syscalls**: Batch operations where possible
- **Zero-copy**: Use capabilities for direct access
- **Small footprint**: Minimal memory usage
- **Fast startup**: Shared libraries reduce load time

## Future Enhancements

- [ ] Dynamic linking for smaller binaries
- [ ] Plugin system for extensibility
- [ ] Hot reloading for development
- [ ] Sandboxing via capability restrictions
- [ ] Performance profiling integration

---

**Total Programs**: 215  
**Categories**: 8  
**Libraries**: 7  
**Build Targets**: 10+  

For questions or contributions, see `DOCUMENTATION.md`
