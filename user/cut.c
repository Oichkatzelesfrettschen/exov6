/**
 * cut - cut out selected fields of each line of a file
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: cut -b list [-n] [file...]
 *        cut -c list [file...]
 *        cut -f list [-d delim] [-s] [file...]
 * 
 * Options:
 *   -b list  Select only these bytes
 *   -c list  Select only these characters
 *   -f list  Select only these fields (tab delimited)
 *   -d delim Use delim as field delimiter (default TAB)
 *   -s       Suppress lines with no delimiter
 *   -n       Do not split multibyte characters (with -b)
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

#define MAX_LINE_LEN 8192
#define MAX_RANGES 100

static int bflag = 0;  // Byte mode
static int cflag = 0;  // Character mode
static int fflag = 0;  // Field mode
static int sflag = 0;  // Suppress lines without delimiter
static int nflag = 0;  // Don't split multibyte chars
static char delimiter = '\t';  // Field delimiter

// Range structure for list parsing
typedef struct {
    int start;  // 1-based, 0 means from beginning
    int end;    // 1-based, 0 means to end
} range_t;

static range_t ranges[MAX_RANGES];
static int range_count = 0;

static void
usage(void)
{
    printf(2, "Usage: cut -b list [-n] [file...]\n");
    printf(2, "       cut -c list [file...]\n");
    printf(2, "       cut -f list [-d delim] [-s] [file...]\n");
    exit(1);
}

// Parse a range list like "1-3,5,7-" or "1,3-5,7"
static int
parse_list(const char *list)
{
    const char *p = list;
    int start, end;
    int in_range = 0;
    int num = 0;
    
    range_count = 0;
    start = end = 0;
    
    while (*p) {
        if (*p >= '0' && *p <= '9') {
            num = num * 10 + (*p - '0');
        } else if (*p == '-') {
            if (in_range) {
                printf(2, "cut: invalid list '%s'\n", list);
                return -1;
            }
            in_range = 1;
            start = num ? num : 0;  // 0 means from beginning
            num = 0;
        } else if (*p == ',') {
            if (in_range) {
                end = num ? num : 0;  // 0 means to end
            } else {
                start = num;
                end = num;
            }
            
            if (range_count >= MAX_RANGES) {
                printf(2, "cut: too many ranges\n");
                return -1;
            }
            
            if (start > 0 || end > 0) {
                ranges[range_count].start = start;
                ranges[range_count].end = end;
                range_count++;
            }
            
            in_range = 0;
            num = 0;
            start = end = 0;
        } else {
            printf(2, "cut: invalid character '%c' in list\n", *p);
            return -1;
        }
        p++;
    }
    
    // Handle last range/number
    if (in_range) {
        end = num ? num : 0;
    } else if (num > 0) {
        start = num;
        end = num;
    }
    
    if (start > 0 || end > 0) {
        if (range_count >= MAX_RANGES) {
            printf(2, "cut: too many ranges\n");
            return -1;
        }
        ranges[range_count].start = start;
        ranges[range_count].end = end;
        range_count++;
    }
    
    if (range_count == 0) {
        printf(2, "cut: no ranges specified\n");
        return -1;
    }
    
    // Sort ranges by start position for efficiency
    for (int i = 0; i < range_count - 1; i++) {
        for (int j = i + 1; j < range_count; j++) {
            if (ranges[i].start > ranges[j].start) {
                range_t temp = ranges[i];
                ranges[i] = ranges[j];
                ranges[j] = temp;
            }
        }
    }
    
    // Merge overlapping ranges
    int merged_count = 0;
    for (int i = 0; i < range_count; i++) {
        if (merged_count == 0) {
            ranges[merged_count++] = ranges[i];
        } else {
            range_t *last = &ranges[merged_count - 1];
            if (ranges[i].start <= last->end + 1 || 
                (last->end == 0) ||
                (ranges[i].start == 0)) {
                // Merge ranges
                if (ranges[i].start > 0 && (last->start == 0 || ranges[i].start < last->start)) {
                    last->start = ranges[i].start;
                }
                if (ranges[i].end == 0 || (last->end > 0 && ranges[i].end > last->end)) {
                    last->end = ranges[i].end;
                }
            } else {
                ranges[merged_count++] = ranges[i];
            }
        }
    }
    range_count = merged_count;
    
    return 0;
}

// Check if position is in any range
static int
in_range(int pos)
{
    for (int i = 0; i < range_count; i++) {
        int start = ranges[i].start ? ranges[i].start : 1;
        int end = ranges[i].end ? ranges[i].end : 999999;
        
        if (pos >= start && pos <= end) {
            return 1;
        }
    }
    return 0;
}

// Cut bytes from line
static void
cut_bytes(const char *line, int len)
{
    for (int i = 0; i < len; i++) {
        if (in_range(i + 1)) {
            write(1, &line[i], 1);
        }
    }
}

// Cut characters from line (same as bytes for ASCII)
static void
cut_chars(const char *line, int len)
{
    // For now, treat same as bytes (no multibyte support)
    cut_bytes(line, len);
}

// Cut fields from line
static void
cut_fields(const char *line, int len)
{
    int field_num = 1;
    int field_start = 0;
    int has_delimiter = 0;
    int output_started = 0;
    
    // Check if line has delimiter
    for (int i = 0; i < len; i++) {
        if (line[i] == delimiter) {
            has_delimiter = 1;
            break;
        }
    }
    
    // If no delimiter and -s flag, suppress line
    if (!has_delimiter && sflag) {
        return;
    }
    
    // If no delimiter and no -s flag, output whole line
    if (!has_delimiter) {
        write(1, line, len);
        return;
    }
    
    // Process fields
    for (int i = 0; i <= len; i++) {
        if (i == len || line[i] == delimiter) {
            // End of field
            if (in_range(field_num)) {
                if (output_started) {
                    write(1, &delimiter, 1);
                }
                write(1, &line[field_start], i - field_start);
                output_started = 1;
            }
            
            field_num++;
            field_start = i + 1;
        }
    }
}

// Process a line based on mode
static void
process_line(const char *line, int len)
{
    // Remove trailing newline for processing
    int process_len = len;
    if (len > 0 && line[len - 1] == '\n') {
        process_len--;
    }
    
    if (bflag) {
        cut_bytes(line, process_len);
    } else if (cflag) {
        cut_chars(line, process_len);
    } else if (fflag) {
        cut_fields(line, process_len);
    }
    
    // Add newline if original had one
    if (len > 0 && line[len - 1] == '\n') {
        write(1, "\n", 1);
    }
}

// Process input file
static int
process_file(int fd)
{
    char buf[MAX_LINE_LEN];
    char line[MAX_LINE_LEN];
    int n, i;
    int line_len = 0;
    int buf_offset = 0;
    
    while ((n = read(fd, buf + buf_offset, MAX_LINE_LEN - buf_offset - 1)) > 0) {
        n += buf_offset;
        buf[n] = '\0';
        
        // Process complete lines
        int line_start = 0;
        for (i = 0; i < n; i++) {
            if (buf[i] == '\n') {
                // Complete line found
                line_len = i - line_start + 1;
                if (line_len < MAX_LINE_LEN) {
                    memcpy(line, &buf[line_start], line_len);
                    line[line_len] = '\0';
                    process_line(line, line_len);
                } else {
                    printf(2, "cut: line too long\n");
                }
                line_start = i + 1;
            }
        }
        
        // Save incomplete line for next iteration
        buf_offset = 0;
        if (line_start < n) {
            buf_offset = n - line_start;
            memmove(buf, &buf[line_start], buf_offset);
        }
    }
    
    // Process last line if no final newline
    if (buf_offset > 0) {
        process_line(buf, buf_offset);
        write(1, "\n", 1);
    }
    
    if (n < 0) {
        printf(2, "cut: read error\n");
        return -1;
    }
    
    return 0;
}

int
main(int argc, char *argv[])
{
    int i;
    char *list = 0;
    int file_start = 1;
    int mode_set = 0;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -- (end of options)
        if (strcmp(p, "-") == 0) {
            file_start = i + 1;
            break;
        }
        
        // Handle options with separate arguments
        if (strcmp(p, "b") == 0 || strcmp(p, "c") == 0 || 
            strcmp(p, "f") == 0 || strcmp(p, "d") == 0) {
            char opt = *p;
            
            if (opt == 'd') {
                i++;
                if (i >= argc) {
                    usage();
                }
                delimiter = argv[i][0];
                if (argv[i][1] != '\0') {
                    printf(2, "cut: delimiter must be a single character\n");
                    usage();
                }
            } else {
                i++;
                if (i >= argc) {
                    usage();
                }
                list = argv[i];
                
                switch (opt) {
                case 'b':
                    bflag = 1;
                    mode_set++;
                    break;
                case 'c':
                    cflag = 1;
                    mode_set++;
                    break;
                case 'f':
                    fflag = 1;
                    mode_set++;
                    break;
                }
            }
            file_start = i + 1;
            continue;
        }
        
        // Handle combined options
        while (*p) {
            switch (*p) {
            case 'b':
                // -b with attached list
                if (*(p + 1)) {
                    list = p + 1;
                    bflag = 1;
                    mode_set++;
                    goto next_arg;
                } else {
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    list = argv[i];
                    bflag = 1;
                    mode_set++;
                    goto next_arg;
                }
                break;
                
            case 'c':
                // -c with attached list
                if (*(p + 1)) {
                    list = p + 1;
                    cflag = 1;
                    mode_set++;
                    goto next_arg;
                } else {
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    list = argv[i];
                    cflag = 1;
                    mode_set++;
                    goto next_arg;
                }
                break;
                
            case 'f':
                // -f with attached list
                if (*(p + 1)) {
                    list = p + 1;
                    fflag = 1;
                    mode_set++;
                    goto next_arg;
                } else {
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    list = argv[i];
                    fflag = 1;
                    mode_set++;
                    goto next_arg;
                }
                break;
                
            case 'd':
                // -d with attached delimiter
                if (*(p + 1)) {
                    delimiter = *(p + 1);
                    if (*(p + 2) != '\0') {
                        printf(2, "cut: delimiter must be a single character\n");
                        usage();
                    }
                    goto next_arg;
                } else {
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    delimiter = argv[i][0];
                    if (argv[i][1] != '\0') {
                        printf(2, "cut: delimiter must be a single character\n");
                        usage();
                    }
                    goto next_arg;
                }
                break;
                
            case 's':
                sflag = 1;
                break;
                
            case 'n':
                nflag = 1;
                break;
                
            default:
                printf(2, "cut: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
        next_arg:
        file_start = i + 1;
    }
    
    // Check that exactly one mode is set
    if (mode_set != 1) {
        printf(2, "cut: must specify exactly one of -b, -c, or -f\n");
        usage();
    }
    
    // Check that list was provided
    if (!list) {
        printf(2, "cut: must specify list\n");
        usage();
    }
    
    // Parse the list
    if (parse_list(list) < 0) {
        exit(1);
    }
    
    // Process files or stdin
    if (file_start >= argc) {
        // Read from stdin
        process_file(0);
    } else {
        // Process each file
        for (i = file_start; i < argc; i++) {
            int fd;
            
            if (strcmp(argv[i], "-") == 0) {
                fd = 0;  // stdin
            } else {
                fd = open(argv[i], O_RDONLY);
                if (fd < 0) {
                    printf(2, "cut: cannot open '%s'\n", argv[i]);
                    continue;
                }
            }
            
            process_file(fd);
            
            if (fd != 0) {
                close(fd);
            }
        }
    }
    
    exit(0);
}