/**
 * paste - merge corresponding lines of files
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: paste [-s] [-d list] file...
 * 
 * Options:
 *   -s       Paste one file at a time instead of in parallel
 *   -d list  Use characters from list instead of TABs
 *   file     Input files (- for stdin)
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"

#define MAX_FILES 20
#define MAX_LINE_LEN 8192
#define MAX_DELIMS 100

static int sflag = 0;          // Serial mode
static char delims[MAX_DELIMS] = "\t";  // Delimiter list
static int delim_count = 1;
static int delim_index = 0;   // Current delimiter index

// File descriptor structure
typedef struct {
    int fd;
    char *name;
    char buffer[MAX_LINE_LEN];
    int buf_pos;
    int buf_len;
    int eof;
} file_info_t;

static file_info_t files[MAX_FILES];
static int file_count = 0;

static void
usage(void)
{
    printf(2, "Usage: paste [-s] [-d list] file...\n");
    exit(1);
}

// Get next delimiter character (cycles through list)
static char
get_delimiter(void)
{
    if (delim_count == 0) return '\t';
    
    char delim = delims[delim_index];
    delim_index = (delim_index + 1) % delim_count;
    return delim;
}

// Reset delimiter index for new line
static void
reset_delimiter(void)
{
    delim_index = 0;
}

// Parse delimiter list (handles \t, \n, \\, \0)
static void
parse_delimiters(const char *list)
{
    int i = 0, j = 0;
    
    while (list[i] && j < MAX_DELIMS - 1) {
        if (list[i] == '\\' && list[i + 1]) {
            switch (list[i + 1]) {
            case 't':
                delims[j++] = '\t';
                i += 2;
                break;
            case 'n':
                delims[j++] = '\n';
                i += 2;
                break;
            case '\\':
                delims[j++] = '\\';
                i += 2;
                break;
            case '0':
                delims[j++] = '\0';
                i += 2;
                break;
            default:
                delims[j++] = list[i + 1];
                i += 2;
                break;
            }
        } else {
            delims[j++] = list[i++];
        }
    }
    
    delim_count = j;
    if (delim_count == 0) {
        delims[0] = '\t';
        delim_count = 1;
    }
}

// Read a line from file
static int
read_line(file_info_t *file, char *line, int max_len)
{
    if (file->eof) return -1;
    
    int line_pos = 0;
    char c;
    
    while (line_pos < max_len - 1) {
        // Refill buffer if needed
        if (file->buf_pos >= file->buf_len) {
            file->buf_len = read(file->fd, file->buffer, MAX_LINE_LEN);
            file->buf_pos = 0;
            
            if (file->buf_len <= 0) {
                file->eof = 1;
                if (line_pos > 0) {
                    line[line_pos] = '\0';
                    return line_pos;
                }
                return -1;
            }
        }
        
        c = file->buffer[file->buf_pos++];
        
        if (c == '\n') {
            line[line_pos] = '\0';
            return line_pos;
        }
        
        line[line_pos++] = c;
    }
    
    line[line_pos] = '\0';
    return line_pos;
}

// Paste files in parallel (default mode)
static void
paste_parallel(void)
{
    char line[MAX_LINE_LEN];
    int any_active = 1;
    int first;
    
    while (any_active) {
        any_active = 0;
        first = 1;
        reset_delimiter();
        
        for (int i = 0; i < file_count; i++) {
            if (!files[i].eof) {
                // Add delimiter before non-first fields
                if (!first) {
                    char delim = get_delimiter();
                    if (delim != '\0') {
                        write(1, &delim, 1);
                    }
                } else {
                    first = 0;
                }
                
                // Read and output line
                if (read_line(&files[i], line, MAX_LINE_LEN) >= 0) {
                    write(1, line, strlen(line));
                    any_active = 1;
                }
            } else if (!first) {
                // File exhausted but need delimiter placeholder
                char delim = get_delimiter();
                if (delim != '\0') {
                    write(1, &delim, 1);
                }
            } else {
                first = 0;
            }
        }
        
        if (any_active) {
            write(1, "\n", 1);
        }
    }
}

// Paste files serially (one file at a time)
static void
paste_serial(void)
{
    char line[MAX_LINE_LEN];
    
    for (int i = 0; i < file_count; i++) {
        int first = 1;
        reset_delimiter();
        
        while (read_line(&files[i], line, MAX_LINE_LEN) >= 0) {
            if (!first) {
                char delim = get_delimiter();
                if (delim != '\0') {
                    write(1, &delim, 1);
                }
            } else {
                first = 0;
            }
            
            write(1, line, strlen(line));
        }
        
        if (!first) {
            write(1, "\n", 1);
        }
    }
}

// Open file or return stdin
static int
open_file(const char *name)
{
    if (strcmp(name, "-") == 0) {
        return 0;  // stdin
    }
    
    int fd = open(name, O_RDONLY);
    if (fd < 0) {
        printf(2, "paste: cannot open '%s'\n", name);
    }
    return fd;
}

int
main(int argc, char *argv[])
{
    int i;
    int file_arg_start = 1;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -- (end of options)
        if (strcmp(p, "-") == 0) {
            file_arg_start = i;
            break;
        }
        
        // Handle -d with separate or attached argument
        if (strcmp(p, "d") == 0) {
            i++;
            if (i >= argc) {
                usage();
            }
            parse_delimiters(argv[i]);
            file_arg_start = i + 1;
            continue;
        }
        
        // Process flags
        while (*p) {
            switch (*p) {
            case 's':
                sflag = 1;
                break;
                
            case 'd':
                // -d with attached argument
                if (*(p + 1)) {
                    parse_delimiters(p + 1);
                    goto next_arg;
                } else {
                    // Separate argument
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    parse_delimiters(argv[i]);
                    goto next_arg;
                }
                break;
                
            default:
                printf(2, "paste: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
        next_arg:
        file_arg_start = i + 1;
    }
    
    // Open input files
    if (file_arg_start >= argc) {
        // No files specified, use stdin
        files[0].fd = 0;
        files[0].name = "-";
        files[0].buf_pos = 0;
        files[0].buf_len = 0;
        files[0].eof = 0;
        file_count = 1;
    } else {
        // Open specified files
        for (i = file_arg_start; i < argc && file_count < MAX_FILES; i++) {
            int fd = open_file(argv[i]);
            if (fd < 0) {
                // Error message already printed
                continue;
            }
            
            files[file_count].fd = fd;
            files[file_count].name = argv[i];
            files[file_count].buf_pos = 0;
            files[file_count].buf_len = 0;
            files[file_count].eof = 0;
            file_count++;
        }
    }
    
    if (file_count == 0) {
        printf(2, "paste: no input files\n");
        exit(1);
    }
    
    // Paste files
    if (sflag) {
        paste_serial();
    } else {
        paste_parallel();
    }
    
    // Close files
    for (i = 0; i < file_count; i++) {
        if (files[i].fd > 0) {
            close(files[i].fd);
        }
    }
    
    exit(0);
}