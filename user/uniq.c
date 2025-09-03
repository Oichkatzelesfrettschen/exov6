/**
 * uniq - report or filter out repeated lines in a file
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: uniq [-c | -d | -u] [-f fields] [-s chars] [input [output]]
 * 
 * Options:
 *   -c  Precede each output line with a count of occurrences
 *   -d  Only output lines that are repeated
 *   -u  Only output lines that are NOT repeated
 *   -i  Case insensitive comparison
 *   -f  Skip first N fields when comparing
 *   -s  Skip first N chars when comparing
 *   -w  Compare at most N characters
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"

#define MAX_LINE_LEN 4096

static int cflag = 0;  // Count occurrences
static int dflag = 0;  // Only duplicates
static int uflag = 0;  // Only unique
static int iflag = 0;  // Case insensitive
static int skip_fields = 0;  // Fields to skip
static int skip_chars = 0;   // Chars to skip
static int max_chars = 0;    // Max chars to compare (0 = all)

typedef struct {
    char text[MAX_LINE_LEN];
    char compare[MAX_LINE_LEN];  // Preprocessed for comparison
    int count;
} line_data_t;

static void
usage(void)
{
    printf(2, "Usage: uniq [-cdui] [-f fields] [-s chars] [-w chars] [input [output]]\n");
    exit(1);
}

// Convert to lowercase for case-insensitive comparison
static char
tolower_char(char c)
{
    if (c >= 'A' && c <= 'Z') {
        return c + ('a' - 'A');
    }
    return c;
}

// Skip specified number of fields (space/tab separated)
static char *
skip_fields_in_line(char *line, int fields)
{
    int field_count = 0;
    char *p = line;
    
    while (field_count < fields && *p) {
        // Skip current field
        while (*p && *p != ' ' && *p != '\t') p++;
        
        // Skip whitespace
        while (*p && (*p == ' ' || *p == '\t')) p++;
        
        field_count++;
    }
    
    return p;
}

// Prepare line for comparison based on options
static void
prepare_compare_string(const char *text, char *compare)
{
    char *src = (char *)text;
    char *dst = compare;
    
    // Skip fields if requested
    if (skip_fields > 0) {
        src = skip_fields_in_line(src, skip_fields);
    }
    
    // Skip chars if requested
    for (int i = 0; i < skip_chars && *src && *src != '\n'; i++) {
        src++;
    }
    
    // Copy with transformations
    int chars_copied = 0;
    while (*src && *src != '\n') {
        // Stop if max_chars reached
        if (max_chars > 0 && chars_copied >= max_chars) {
            break;
        }
        
        // Apply case transformation if needed
        if (iflag) {
            *dst = tolower_char(*src);
        } else {
            *dst = *src;
        }
        
        src++;
        dst++;
        chars_copied++;
    }
    
    *dst = '\0';
}

// Compare two prepared strings
static int
lines_equal(const char *s1, const char *s2)
{
    return strcmp(s1, s2) == 0;
}

// Output a line with appropriate formatting
static void
output_line(int fd, const line_data_t *line)
{
    if (cflag) {
        // Output with count
        char countbuf[32];
        int len = 0;
        int count = line->count;
        
        // Convert count to string
        if (count == 0) {
            countbuf[0] = '0';
            len = 1;
        } else {
            char temp[32];
            int i = 0;
            while (count > 0) {
                temp[i++] = '0' + (count % 10);
                count /= 10;
            }
            // Reverse
            for (int j = 0; j < i; j++) {
                countbuf[j] = temp[i - j - 1];
            }
            len = i;
        }
        
        // Right-align count in 7-char field
        for (int i = 0; i < 7 - len; i++) {
            write(fd, " ", 1);
        }
        write(fd, countbuf, len);
        write(fd, " ", 1);
    }
    
    // Output the line
    write(fd, line->text, strlen(line->text));
    if (line->text[strlen(line->text) - 1] != '\n') {
        write(fd, "\n", 1);
    }
}

// Process input and filter duplicates
static int
process_input(int in_fd, int out_fd)
{
    char buf[MAX_LINE_LEN];
    line_data_t current, previous;
    int has_previous = 0;
    int n, i;
    int line_start = 0;
    int buf_len = 0;
    
    // Initialize
    memset(&previous, 0, sizeof(previous));
    previous.count = 0;
    
    while ((n = read(in_fd, buf + buf_len, MAX_LINE_LEN - buf_len - 1)) > 0) {
        n += buf_len;
        buf[n] = '\0';
        
        // Process complete lines
        line_start = 0;
        for (i = 0; i < n; i++) {
            if (buf[i] == '\n' || i == n - 1) {
                // Extract line
                int line_end = (buf[i] == '\n') ? i + 1 : n;
                int line_len = line_end - line_start;
                
                if (line_len > 0 && line_len < MAX_LINE_LEN) {
                    // Copy line
                    memcpy(current.text, &buf[line_start], line_len);
                    current.text[line_len] = '\0';
                    
                    // Prepare comparison string
                    prepare_compare_string(current.text, current.compare);
                    current.count = 1;
                    
                    if (has_previous) {
                        // Compare with previous line
                        if (lines_equal(current.compare, previous.compare)) {
                            // Duplicate found
                            previous.count++;
                        } else {
                            // Different line - output previous if needed
                            int should_output = 0;
                            
                            if (!cflag && !dflag && !uflag) {
                                // Default: output one copy of each line
                                should_output = 1;
                            } else if (dflag && previous.count > 1) {
                                // -d: only duplicates
                                should_output = 1;
                            } else if (uflag && previous.count == 1) {
                                // -u: only unique
                                should_output = 1;
                            } else if (cflag) {
                                // -c: output all with counts
                                should_output = 1;
                            }
                            
                            if (should_output) {
                                output_line(out_fd, &previous);
                            }
                            
                            // Current becomes previous
                            memcpy(&previous, &current, sizeof(line_data_t));
                        }
                    } else {
                        // First line
                        memcpy(&previous, &current, sizeof(line_data_t));
                        has_previous = 1;
                    }
                }
                
                line_start = line_end;
            }
        }
        
        // Move incomplete line to beginning
        buf_len = 0;
        if (line_start < n) {
            buf_len = n - line_start;
            memmove(buf, &buf[line_start], buf_len);
        }
    }
    
    // Output last line if needed
    if (has_previous) {
        int should_output = 0;
        
        if (!cflag && !dflag && !uflag) {
            should_output = 1;
        } else if (dflag && previous.count > 1) {
            should_output = 1;
        } else if (uflag && previous.count == 1) {
            should_output = 1;
        } else if (cflag) {
            should_output = 1;
        }
        
        if (should_output) {
            output_line(out_fd, &previous);
        }
    }
    
    if (n < 0) {
        printf(2, "uniq: read error\n");
        return -1;
    }
    
    return 0;
}

// Parse number from string
static int
parse_number(const char *str)
{
    int num = 0;
    while (*str >= '0' && *str <= '9') {
        num = num * 10 + (*str - '0');
        str++;
    }
    return num;
}

int
main(int argc, char *argv[])
{
    int i;
    int in_fd = 0;   // stdin
    int out_fd = 1;  // stdout
    char *input_file = 0;
    char *output_file = 0;
    int file_arg_index = 1;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -- (end of options)
        if (strcmp(p, "-") == 0) {
            file_arg_index = i + 1;
            break;
        }
        
        // Handle options with arguments
        if (strcmp(p, "f") == 0 || strcmp(p, "s") == 0 || strcmp(p, "w") == 0) {
            char opt = *p;
            i++;
            if (i >= argc) {
                usage();
            }
            
            int value = parse_number(argv[i]);
            if (value < 0) {
                printf(2, "uniq: invalid number '%s'\n", argv[i]);
                usage();
            }
            
            switch (opt) {
            case 'f':
                skip_fields = value;
                break;
            case 's':
                skip_chars = value;
                break;
            case 'w':
                max_chars = value;
                break;
            }
            file_arg_index = i + 1;
            continue;
        }
        
        // Handle flags
        while (*p) {
            switch (*p) {
            case 'c':
                cflag = 1;
                dflag = 0;
                uflag = 0;
                break;
            case 'd':
                dflag = 1;
                cflag = 0;
                uflag = 0;
                break;
            case 'u':
                uflag = 1;
                cflag = 0;
                dflag = 0;
                break;
            case 'i':
                iflag = 1;
                break;
            case 'f':
            case 's':
            case 'w':
                // These need arguments
                if (*(p + 1)) {
                    // Attached argument
                    int value = parse_number(p + 1);
                    if (value < 0) {
                        printf(2, "uniq: invalid number '%s'\n", p + 1);
                        usage();
                    }
                    
                    switch (*p) {
                    case 'f':
                        skip_fields = value;
                        break;
                    case 's':
                        skip_chars = value;
                        break;
                    case 'w':
                        max_chars = value;
                        break;
                    }
                    goto next_arg;
                } else {
                    // Separate argument
                    i++;
                    if (i >= argc) {
                        usage();
                    }
                    
                    int value = parse_number(argv[i]);
                    if (value < 0) {
                        printf(2, "uniq: invalid number '%s'\n", argv[i]);
                        usage();
                    }
                    
                    switch (*p) {
                    case 'f':
                        skip_fields = value;
                        break;
                    case 's':
                        skip_chars = value;
                        break;
                    case 'w':
                        max_chars = value;
                        break;
                    }
                    goto next_arg;
                }
                break;
            default:
                printf(2, "uniq: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
        next_arg:
        file_arg_index = i + 1;
    }
    
    // Get input and output files
    if (file_arg_index < argc) {
        input_file = argv[file_arg_index];
        if (file_arg_index + 1 < argc) {
            output_file = argv[file_arg_index + 1];
        }
    }
    
    // Open input file
    if (input_file && strcmp(input_file, "-") != 0) {
        in_fd = open(input_file, O_RDONLY);
        if (in_fd < 0) {
            printf(2, "uniq: cannot open '%s'\n", input_file);
            exit(1);
        }
    }
    
    // Open output file
    if (output_file && strcmp(output_file, "-") != 0) {
        out_fd = open(output_file, O_WRONLY | O_CREATE | O_TRUNC);
        if (out_fd < 0) {
            printf(2, "uniq: cannot create '%s'\n", output_file);
            if (in_fd > 0) close(in_fd);
            exit(1);
        }
    }
    
    // Process input
    int ret = process_input(in_fd, out_fd);
    
    // Close files
    if (in_fd > 0) close(in_fd);
    if (out_fd > 1) close(out_fd);
    
    exit(ret < 0 ? 1 : 0);
}