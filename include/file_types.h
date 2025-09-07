#pragma once

// File types for filesystem
#define T_DIR     1   // Directory
#define T_FILE    2   // Regular file
#define T_DEV     3   // Device file
#define T_SYMLINK 4   // Symbolic link (future)

// File permissions (POSIX-like)
#define S_IRUSR   0400  // User read
#define S_IWUSR   0200  // User write
#define S_IXUSR   0100  // User execute
#define S_IRGRP   0040  // Group read
#define S_IWGRP   0020  // Group write
#define S_IXGRP   0010  // Group execute
#define S_IROTH   0004  // Other read
#define S_IWOTH   0002  // Other write
#define S_IXOTH   0001  // Other execute

// Default permissions
#define DEFAULT_FILE_MODE  (S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH)
#define DEFAULT_DIR_MODE   (S_IRUSR | S_IWUSR | S_IXUSR | S_IRGRP | S_IXGRP | S_IROTH | S_IXOTH)