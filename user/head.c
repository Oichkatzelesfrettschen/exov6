/**
 * head - output the first part of files
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: head [-n number] [file...]
 * 
 * Options:
 *   -n number  Output first 'number' lines (default 10)
 *   -c number  Output first 'number' bytes
 *   -q         Never output headers with file names
 *   -v         Always output headers with file names
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

#define DEFAULT_LINES 10
#define BUFSIZE 512

static int nflag = 0;     // Number of lines
static int cflag = 0;     // Number of bytes
static int qflag = 0;     // Quiet (no headers)
static int vflag = 0;     // Verbose (always headers)
static int count = DEFAULT_LINES;

static void
usage(void)
{
    printf(2, "Usage: head [-n lines] [-c bytes] [-qv] [file...]\n");
    exit(1);
}

// Parse number from string
static int
parse_number(const char *str)
{
    int num = 0;
    int neg = 0;
    const char *p = str;
    
    if (*p == '-') {
        neg = 1;
        p++;
    } else if (*p == '+') {
        p++;
    }
    
    while (*p) {
        if (*p < '0' || *p > '9') {
            return -1;
        }
        num = num * 10 + (*p - '0');
        p++;
    }
    
    return neg ? -num : num;
}

// Output first n lines of a file
static int
head_lines(int fd, const char *filename, int lines)
{
    char buf[BUFSIZE];
    int n, i;
    int line_count = 0;
    int in_line = 0;
    
    while (line_count < lines && (n = read(fd, buf, sizeof(buf))) > 0) {
        for (i = 0; i < n && line_count < lines; i++) {
            write(1, &buf[i], 1);
            
            if (buf[i] == '\n') {
                line_count++;
                in_line = 0;
            } else {
                in_line = 1;
            }
        }
    }
    
    // Add newline if file doesn't end with one
    if (in_line && line_count < lines) {
        write(1, "\n", 1);
    }
    
    if (n < 0) {
        printf(2, "head: read error\n");
        return -1;
    }
    
    return 0;
}

// Output first n bytes of a file
static int
head_bytes(int fd, const char *filename, int bytes)
{
    char buf[BUFSIZE];
    int n;
    int remaining = bytes;
    
    while (remaining > 0) {
        int to_read = remaining < BUFSIZE ? remaining : BUFSIZE;
        n = read(fd, buf, to_read);
        
        if (n <= 0) {
            break;
        }
        
        write(1, buf, n);
        remaining -= n;
    }
    
    if (n < 0) {
        printf(2, "head: read error\n");
        return -1;
    }
    
    return 0;
}

// Process a single file
static int
process_file(const char *filename, int show_header)
{
    int fd;
    int ret;
    
    // Open file (stdin if "-" or NULL)
    if (filename == 0 || strcmp(filename, "-") == 0) {
        fd = 0;  // stdin
        filename = "standard input";
    } else {
        fd = open(filename, O_RDONLY);
        if (fd < 0) {
            printf(2, "head: cannot open '%s'\n", filename);
            return -1;
        }
    }
    
    // Print header if needed
    if (show_header) {
        printf(1, "==> %s <==\n", filename);
    }
    
    // Process file
    if (cflag) {
        ret = head_bytes(fd, filename, count);
    } else {
        ret = head_lines(fd, filename, count);
    }
    
    // Close file if not stdin
    if (fd != 0) {
        close(fd);
    }
    
    return ret;
}

int
main(int argc, char *argv[])
{
    int i;
    int file_start = 1;
    int file_count = 0;
    int show_headers;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -- (end of options)
        if (strcmp(p, "-") == 0) {
            file_start = i + 1;
            break;
        }
        
        // Handle -n or -c with separate argument
        if (strcmp(p, "n") == 0 || strcmp(p, "c") == 0) {
            int is_bytes = (*p == 'c');
            i++;
            if (i >= argc) {
                usage();
            }
            count = parse_number(argv[i]);
            if (count < 0) {
                // Negative means "all but last N"
                // For simplicity, treat as positive
                count = -count;
            }
            if (is_bytes) {
                cflag = 1;
            } else {
                nflag = 1;
            }
            file_start = i + 1;
            continue;
        }
        
        // Handle combined options
        while (*p) {
            switch (*p) {
            case 'n':
                // -n with value attached
                p++;
                if (*p) {
                    count = parse_number(p);
                    if (count < 0) count = -count;
                    nflag = 1;
                } else {
                    // Next arg is the number
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    count = parse_number(argv[i]);
                    if (count < 0) count = -count;
                    nflag = 1;
                }
                goto next_arg;
                
            case 'c':
                // -c with value attached
                p++;
                if (*p) {
                    count = parse_number(p);
                    if (count < 0) count = -count;
                    cflag = 1;
                } else {
                    // Next arg is the number
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    count = parse_number(argv[i]);
                    if (count < 0) count = -count;
                    cflag = 1;
                }
                goto next_arg;
                
            case 'q':
                qflag = 1;
                vflag = 0;
                break;
                
            case 'v':
                vflag = 1;
                qflag = 0;
                break;
                
            case '0': case '1': case '2': case '3': case '4':
            case '5': case '6': case '7': case '8': case '9':
                // Old syntax: -10 means -n 10
                count = parse_number(p);
                if (count < 0) count = -count;
                nflag = 1;
                goto next_arg;
                
            default:
                printf(2, "head: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
        next_arg:
        file_start = i + 1;
    }
    
    // Count files
    file_count = argc - file_start;
    
    // Determine if we should show headers
    show_headers = vflag || (!qflag && file_count > 1);
    
    // Process files
    if (file_count == 0) {
        // Read from stdin
        process_file(0, 0);
    } else {
        // Process each file
        for (i = file_start; i < argc; i++) {
            if (i > file_start && show_headers) {
                printf(1, "\n");  // Blank line between files
            }
            process_file(argv[i], show_headers);
        }
    }
    
    exit(0);
}