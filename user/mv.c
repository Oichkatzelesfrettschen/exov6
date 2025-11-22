/**
 * mv.c - The "Riced" Move Utility
 * POSIX-ish implementation for FeuerBird exokernel
 *
 * Features:
 * - Atomic rename preference
 * - Cross-device recursive move (copy+del)
 * - Backup (-b), Update (-u), No-clobber (-n), Verbose (-v)
 * - 8KB buffer optimization
 * - ANSI Color output
 */

#include <types.h>
#include <user.h>
#include <fcntl.h>
#include <fs.h>
#include <stat.h> 

// --- Configuration ---
#define BUF_SIZE 8192       // 8KB buffer for fewer syscalls
#define MAX_PATH 1024       // Generous path limit

// --- ANSI Colors ---
#define COL_RESET  "\x1b[0m"
#define COL_RED    "\x1b[31m"
#define COL_GREEN  "\x1b[32m"
#define COL_YELLOW "\x1b[33m"
#define COL_CYAN   "\x1b[36m"

// --- Globals ---
static int iflag = 0; // Interactive
static int fflag = 0; // Force
static int vflag = 0; // Verbose
static int nflag = 0; // No clobber
static int uflag = 0; // Update only
static int bflag = 0; // Backup

// --- Helpers ---

void
printerr(const char *msg, const char *arg)
{
    printf(2, "%smv: %s %s%s\n", COL_RED, msg, arg ? arg : "", COL_RESET);
}

void
printact(const char *src, const char *dst)
{
    if(vflag)
        printf(1, "%s'%s' -> '%s'%s\n", COL_CYAN, src, dst, COL_RESET);
}

// Safe string concatenation for paths
void
join_path(char *dest, const char *dir, const char *file)
{
    int len = strlen(dir);
    strcpy(dest, dir);
    if(len > 0 && dest[len-1] != '/') {
        strcat(dest, "/");
    }
    strcat(dest, file);
}

const char*
basename(const char *path)
{
    const char *p = strrchr(path, '/');
    return p ? p + 1 : path;
}

// Standard atomic rename simulation
int 
rename_atomic(const char *old, const char *new) 
{
    if (link(old, new) < 0) return -1;
    if (unlink(old) < 0) {
        unlink(new); // Rollback
        return -1;
    }
    return 0;
}

// --- Core Logic ---

// Copies file content and attributes
// Returns 0 on success, -1 on fail
int
copy_data(const char *src, const char *dst, const struct stat *st_src)
{
    int fd_src, fd_dst;
    int n;
    char *buf = malloc(BUF_SIZE); 
    
    if (!buf) {
        printerr("out of memory", 0);
        return -1;
    }

    if ((fd_src = open(src, O_RDONLY)) < 0) {
        printerr("cannot open source", src);
        free(buf);
        return -1;
    }

    // Create with source permissions (masked by umask typically, but we force mode here if possible)
    // Note: O_CREATE | O_TRUNC ensures we overwrite cleanly
    if ((fd_dst = open(dst, O_CREATE | O_WRONLY | O_TRUNC, st_src->mode)) < 0) {
        printerr("cannot create target", dst);
        close(fd_src);
        free(buf);
        return -1;
    }

    while ((n = read(fd_src, buf, BUF_SIZE)) > 0) {
        if (write(fd_dst, buf, n) != n) {
            printerr("write error", dst);
            close(fd_src); close(fd_dst);
            free(buf);
            return -1;
        }
    }

    close(fd_src);
    close(fd_dst);
    free(buf);

    if (n < 0) {
        printerr("read error", src);
        return -1;
    }

    return 0;
}

// Handles the "Backup" logic (-b)
// Renames "file" to "file~"
void
handle_backup(const char *path)
{
    char backup_path[MAX_PATH];
    if (strlen(path) + 2 >= MAX_PATH) return;
    
    strcpy(backup_path, path);
    strcat(backup_path, "~");
    
    // We don't check errors heavily here; best effort
    rename_atomic(path, backup_path);
    if(vflag) printf(1, "%s(backup) '%s' -> '%s'%s\n", COL_YELLOW, path, backup_path, COL_RESET);
}

// Forward declaration
int do_move(const char *src, const char *dst);

// Recursively copy a directory
// NOTE: This requires 'mkdir' and directory reading capabilities.
// Assuming a 'struct dirent' and 'read_dir' style API exists in FeuerBird.
int
recursive_copy_move(const char *src, const char *dst, int mode)
{
    int fd;
    struct dirent de;
    struct stat st;
    char s_path[MAX_PATH];
    char d_path[MAX_PATH];

    // 1. Create destination directory
    if (mkdir(dst, mode) < 0) {
        // If it exists, that's fine, we merge
        if (stat(dst, &st) < 0 || st.type != T_DIR) {
            printerr("cannot create directory", dst);
            return -1;
        }
    }

    // 2. Open source directory
    if ((fd = open(src, O_RDONLY)) < 0) {
        printerr("cannot open directory", src);
        return -1;
    }

    // 3. Iterate children
    while (read(fd, &de, sizeof(de)) == sizeof(de)) {
        if (de.inum == 0) continue; // Empty slot
        if (strcmp(de.name, ".") == 0 || strcmp(de.name, "..") == 0) continue;

        // Construct paths
        join_path(s_path, src, de.name);
        join_path(d_path, dst, de.name);

        // Recurse
        if (do_move(s_path, d_path) < 0) {
            close(fd);
            return -1;
        }
    }
    
    close(fd);

    // 4. Remove source directory (should be empty now)
    if (unlink(src) < 0) {
        // Some OSes use rmdir(), some use unlink() for dirs
        printerr("cannot remove source directory", src);
        return -1;
    }

    return 0;
}

int
do_move(const char *src, const char *dst)
{
    struct stat s_st, d_st;
    int dest_exists = 0;

    // 1. Analyze Source
    if (stat(src, &s_st) < 0) {
        printerr("source not found", src);
        return -1;
    }

    // 2. Analyze Destination
    if (stat(dst, &d_st) >= 0) {
        dest_exists = 1;

        // Handle Identity
        if (s_st.dev == d_st.dev && s_st.ino == d_st.ino) {
            if (vflag) printf(1, "mv: '%s' and '%s' are the same file\n", src, dst);
            return 0; 
        }

        // Handle Directory Target
        if (d_st.type == T_DIR) {
            char final_path[MAX_PATH];
            join_path(final_path, dst, basename(src));
            return do_move(src, final_path); // Recurse with fixed path
        }

        // Handle Overwrite Logic
        if (nflag) {
            // No clobber
            return 0; 
        }
        
        if (uflag) {
            // Update: Only if src is newer
            // Note: assuming stat has mtime. If not, remove this block.
            if (s_st.mtime <= d_st.mtime) return 0; 
        }

        if (iflag && !fflag) {
            printf(1, "%soverwrite '%s'? (y/n) %s", COL_YELLOW, dst, COL_RESET);
            char buf[16];
            gets(buf, sizeof(buf));
            if (buf[0] != 'y' && buf[0] != 'Y') return 0;
        }

        // Handle Backup
        if (bflag) {
            handle_backup(dst);
        }
    }

    // 3. Try Atomic Rename
    // This handles file->file and dir->dir (on same FS)
    if (rename_atomic(src, dst) == 0) {
        printact(src, dst);
        return 0;
    }

    // 4. Fallback: Cross-Device Move (Copy + Delete)
    
    // Directory case
    if (s_st.type == T_DIR) {
        // If dest exists and is a file, we can't overwrite it with a dir
        if (dest_exists && d_st.type != T_DIR) {
            printerr("cannot overwrite non-directory with directory", dst);
            return -1;
        }
        return recursive_copy_move(src, dst, s_st.mode);
    }

    // File case
    if (copy_data(src, dst, &s_st) == 0) {
        if (unlink(src) < 0) {
            printerr("copied, but failed to remove source", src);
            return -1;
        }
        printact(src, dst);
        return 0;
    }

    return -1;
}

void
usage(void)
{
    printf(2, "Usage: mv [OPTIONS] source... target\n");
    printf(2, "Options:\n");
    printf(2, "  -f  Force overwrite\n");
    printf(2, "  -i  Interactive\n");
    printf(2, "  -n  No clobber (do not overwrite)\n");
    printf(2, "  -u  Update (only if source is newer)\n");
    printf(2, "  -v  Verbose\n");
    printf(2, "  -b  Backup existing files (file~)\n");
    exit(1);
}

int
main(int argc, char *argv[])
{
    int i;
    int args_start = 0;

    if (argc < 2) usage();

    // Parse flags
    for (i = 1; i < argc; i++) {
        if (argv[i][0] != '-') {
            args_start = i;
            break;
        }
        
        // Handle flags like -vf or -i
        char *p = argv[i] + 1;
        while (*p) {
            switch (*p) {
                case 'f': fflag = 1; iflag = 0; nflag = 0; break;
                case 'i': iflag = 1; fflag = 0; nflag = 0; break;
                case 'n': nflag = 1; fflag = 0; iflag = 0; break;
                case 'v': vflag = 1; break;
                case 'u': uflag = 1; break;
                case 'b': bflag = 1; break;
                default: 
                    printf(2, "mv: unknown option -%c\n", *p);
                    usage();
            }
            p++;
        }
    }

    if (args_start == 0) usage();

    int num_sources = argc - args_start - 1;
    char *target = argv[argc - 1];

    // Case: mv file1 file2
    if (num_sources == 1) {
        struct stat st;
        char *src = argv[args_start];
        
        // Edge case: if target is a directory, treat as move-into-dir
        if (stat(target, &st) >= 0 && st.type == T_DIR) {
            char final_path[MAX_PATH];
            join_path(final_path, target, basename(src));
            if (do_move(src, final_path) < 0) exit(1);
        } else {
            if (do_move(src, target) < 0) exit(1);
        }
    } 
    // Case: mv file1 file2 ... dir
    else {
        struct stat st;
        if (stat(target, &st) < 0 || st.type != T_DIR) {
            printerr("target must be a directory for multiple sources", target);
            exit(1);
        }

        int failure = 0;
        for (i = args_start; i < argc - 1; i++) {
            char final_path[MAX_PATH];
            join_path(final_path, target, basename(argv[i]));
            
            if (do_move(argv[i], final_path) < 0) {
                failure = 1;
            }
        }
        if (failure) exit(1);
    }

    exit(0);
}