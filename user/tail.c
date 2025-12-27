/**
 * tail - output the last part of files
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: tail [-f] [-c number | -n number] [file...]
 * 
 * Options:
 *   -n number  Output last 'number' lines (default 10)
 *   -c number  Output last 'number' bytes
 *   -f         Follow file (output appended data)
 *   -F         Follow and retry if file doesn't exist
 *   -q         Never output headers with file names
 *   -v         Always output headers with file names
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"
#include "fs.h"

#define DEFAULT_LINES 10
#define BUFSIZE 4096
#define MAX_LINE_SIZE 8192

static int nflag = 1;      // Number of lines mode (default)
static int cflag = 0;      // Number of bytes mode
static int fflag = 0;      // Follow mode
static int Fflag = 0;      // Follow with retry
static int qflag = 0;      // Quiet (no headers)
static int vflag = 0;      // Verbose (always headers)
static long count = DEFAULT_LINES;
static int from_start = 0; // If count starts with '+', tail from start

// Circular buffer for efficient line storage
typedef struct {
    char **lines;
    int *lengths;
    int capacity;
    int size;
    int head;
} line_buffer_t;

static void
usage(void)
{
    printf(2, "Usage: tail [-f] [-c number | -n number] [-qv] [file...]\n");
    exit(1);
}

// Parse number with optional + prefix
static long
parse_number(const char *str)
{
    long num = 0;
    const char *p = str;
    
    // Check for + prefix (from start)
    if (*p == '+') {
        from_start = 1;
        p++;
    } else if (*p == '-') {
        p++;  // Skip minus (from end is default)
    }
    
    while (*p) {
        if (*p < '0' || *p > '9') {
            return -1;
        }
        num = num * 10 + (*p - '0');
        p++;
    }
    
    return num;
}

// Initialize line buffer
static line_buffer_t *
init_line_buffer(int capacity)
{
    line_buffer_t *buf = malloc(sizeof(line_buffer_t));
    if (!buf) return NULL;
    
    buf->lines = malloc(sizeof(char*) * capacity);
    buf->lengths = malloc(sizeof(int) * capacity);
    buf->capacity = capacity;
    buf->size = 0;
    buf->head = 0;
    
    for (int i = 0; i < capacity; i++) {
        buf->lines[i] = malloc(MAX_LINE_SIZE);
        if (!buf->lines[i]) {
            // Cleanup on failure
            for (int j = 0; j < i; j++) {
                free(buf->lines[j]);
            }
            free(buf->lines);
            free(buf->lengths);
            free(buf);
            return NULL;
        }
    }
    
    return buf;
}

// Add line to circular buffer
static void
add_line(line_buffer_t *buf, const char *line, int len)
{
    int idx;
    
    if (buf->size < buf->capacity) {
        idx = buf->size++;
    } else {
        idx = buf->head;
        buf->head = (buf->head + 1) % buf->capacity;
    }
    
    memcpy(buf->lines[idx], line, len);
    buf->lengths[idx] = len;
}

// Print all lines in buffer
static void
print_buffer(line_buffer_t *buf)
{
    int start = (buf->size == buf->capacity) ? buf->head : 0;
    
    for (int i = 0; i < buf->size; i++) {
        int idx = (start + i) % buf->capacity;
        write(1, buf->lines[idx], buf->lengths[idx]);
    }
}

// Free line buffer
static void
free_line_buffer(line_buffer_t *buf)
{
    if (!buf) return;
    
    for (int i = 0; i < buf->capacity; i++) {
        free(buf->lines[i]);
    }
    free(buf->lines);
    free(buf->lengths);
    free(buf);
}

// Output last n lines from file descriptor
static int
tail_lines(int fd, const char *filename, long lines, int from_beginning)
{
    char buf[BUFSIZE];
    char line[MAX_LINE_SIZE];
    int n, i;
    int line_len = 0;
    long line_count = 0;
    line_buffer_t *line_buf = NULL;
    
    if (from_beginning) {
        // Skip first (lines-1) lines, then output rest
        while ((n = read(fd, buf, sizeof(buf))) > 0) {
            for (i = 0; i < n; i++) {
                if (line_len < MAX_LINE_SIZE - 1) {
                    line[line_len++] = buf[i];
                }
                
                if (buf[i] == '\n') {
                    line_count++;
                    if (line_count >= lines) {
                        // Output this line and all following
                        write(1, line, line_len);
                        // Output rest of buffer
                        if (i + 1 < n) {
                            write(1, &buf[i + 1], n - i - 1);
                        }
                        // Output everything else
                        while ((n = read(fd, buf, sizeof(buf))) > 0) {
                            write(1, buf, n);
                        }
                        return 0;
                    }
                    line_len = 0;
                }
            }
        }
    } else {
        // Store last 'lines' lines
        line_buf = init_line_buffer(lines);
        if (!line_buf) {
            printf(2, "tail: out of memory\n");
            return -1;
        }
        
        while ((n = read(fd, buf, sizeof(buf))) > 0) {
            for (i = 0; i < n; i++) {
                if (line_len < MAX_LINE_SIZE - 1) {
                    line[line_len++] = buf[i];
                }
                
                if (buf[i] == '\n' || line_len == MAX_LINE_SIZE - 1) {
                    add_line(line_buf, line, line_len);
                    line_len = 0;
                }
            }
        }
        
        // Handle last line without newline
        if (line_len > 0) {
            line[line_len++] = '\n';
            add_line(line_buf, line, line_len);
        }
        
        // Print buffered lines
        print_buffer(line_buf);
        free_line_buffer(line_buf);
    }
    
    if (n < 0) {
        printf(2, "tail: read error\n");
        return -1;
    }
    
    return 0;
}

// Output last n bytes from file descriptor
static int
tail_bytes(int fd, const char *filename, long bytes, int from_beginning)
{
    char buf[BUFSIZE];
    char *circular_buf;
    long circular_size;
    long circular_pos = 0;
    int n;
    
    if (from_beginning) {
        // Skip first (bytes-1) bytes, then output rest
        long skipped = 0;
        while (skipped < bytes - 1) {
            long to_skip = bytes - 1 - skipped;
            if (to_skip > BUFSIZE) to_skip = BUFSIZE;
            
            n = read(fd, buf, to_skip);
            if (n <= 0) break;
            skipped += n;
        }
        
        // Output everything else
        while ((n = read(fd, buf, sizeof(buf))) > 0) {
            write(1, buf, n);
        }
    } else {
        // Use circular buffer for last 'bytes' bytes
        circular_size = bytes < BUFSIZE ? bytes : bytes;
        circular_buf = malloc(circular_size);
        if (!circular_buf) {
            printf(2, "tail: out of memory\n");
            return -1;
        }
        
        long total_read = 0;
        while ((n = read(fd, buf, sizeof(buf))) > 0) {
            for (int i = 0; i < n; i++) {
                circular_buf[circular_pos] = buf[i];
                circular_pos = (circular_pos + 1) % circular_size;
                total_read++;
            }
        }
        
        // Output circular buffer contents
        if (total_read < circular_size) {
            // File smaller than requested bytes
            write(1, circular_buf, total_read);
        } else {
            // Output from current position to end, then from start to position
            write(1, &circular_buf[circular_pos], circular_size - circular_pos);
            write(1, circular_buf, circular_pos);
        }
        
        free(circular_buf);
    }
    
    if (n < 0) {
        printf(2, "tail: read error\n");
        return -1;
    }
    
    return 0;
}

// Follow file for new data
static void
follow_file(int fd, const char *filename)
{
    char buf[BUFSIZE];
    int n;
    struct stat st1, st2;
    
    // Get initial file info
    if (fstat(fd, &st1) < 0) {
        return;
    }
    
    printf(1, "\n==> %s <==\n", filename);
    
    while (1) {
        // Read any new data
        while ((n = read(fd, buf, sizeof(buf))) > 0) {
            write(1, buf, n);
        }
        
        // Sleep briefly
        sleep(100);  // 1 second in feuerbird ticks
        
        // Check if file has been replaced (for -F)
        if (Fflag) {
            if (stat(filename, &st2) >= 0) {
                if (st1.ino != st2.ino || st1.dev != st2.dev) {
                    // File has been replaced
                    close(fd);
                    fd = open(filename, O_RDONLY);
                    if (fd < 0) {
                        // File deleted, wait and retry
                        sleep(100);
                        continue;
                    }
                    st1 = st2;
                    printf(1, "\n==> %s <== (file recreated)\n", filename);
                }
            }
        }
    }
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
            printf(2, "tail: cannot open '%s'\n", filename);
            return -1;
        }
    }
    
    // Print header if needed
    if (show_header) {
        printf(1, "==> %s <==\n", filename);
    }
    
    // Process file
    if (cflag) {
        ret = tail_bytes(fd, filename, count, from_start);
    } else {
        ret = tail_lines(fd, filename, count, from_start);
    }
    
    // Follow mode
    if (fflag || Fflag) {
        follow_file(fd, filename);
        // Never returns
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
                printf(2, "tail: invalid number '%s'\n", argv[i]);
                usage();
            }
            if (is_bytes) {
                cflag = 1;
                nflag = 0;
            } else {
                nflag = 1;
                cflag = 0;
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
                    if (count < 0) {
                        printf(2, "tail: invalid number '%s'\n", p);
                        usage();
                    }
                    nflag = 1;
                    cflag = 0;
                } else {
                    // Next arg is the number
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    count = parse_number(argv[i]);
                    if (count < 0) {
                        printf(2, "tail: invalid number '%s'\n", argv[i]);
                        usage();
                    }
                    nflag = 1;
                    cflag = 0;
                }
                goto next_arg;
                
            case 'c':
                // -c with value attached
                p++;
                if (*p) {
                    count = parse_number(p);
                    if (count < 0) {
                        printf(2, "tail: invalid number '%s'\n", p);
                        usage();
                    }
                    cflag = 1;
                    nflag = 0;
                } else {
                    // Next arg is the number
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    count = parse_number(argv[i]);
                    if (count < 0) {
                        printf(2, "tail: invalid number '%s'\n", argv[i]);
                        usage();
                    }
                    cflag = 1;
                    nflag = 0;
                }
                goto next_arg;
                
            case 'f':
                fflag = 1;
                break;
                
            case 'F':
                Fflag = 1;
                fflag = 1;
                break;
                
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
            case '+':
                // Old syntax: -10 means -n 10, +10 means -n +10
                count = parse_number(p);
                if (count < 0) {
                    printf(2, "tail: invalid number '%s'\n", p);
                    usage();
                }
                nflag = 1;
                cflag = 0;
                goto next_arg;
                
            default:
                printf(2, "tail: invalid option -- '%c'\n", *p);
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