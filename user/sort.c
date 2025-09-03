/**
 * sort - sort lines of text files
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: sort [-nru] [-k field] [-t delim] [file...]
 * 
 * Options:
 *   -n  Numeric sort
 *   -r  Reverse sort
 *   -u  Unique (remove duplicates)
 *   -k  Key field for sorting
 *   -t  Field delimiter
 *   -f  Case-insensitive
 *   -b  Ignore leading blanks
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"

#define MAX_LINES 10000
#define MAX_LINE_LEN 4096
#define MAX_FIELDS 100

static int nflag = 0;  // Numeric sort
static int rflag = 0;  // Reverse sort
static int uflag = 0;  // Unique
static int fflag = 0;  // Fold case
static int bflag = 0;  // Ignore blanks
static int kflag = 0;  // Key field
static int key_field = 1;  // Field number (1-based)
static char delimiter = '\t';  // Field delimiter

// Line structure
typedef struct {
    char *text;
    int len;
    char *key;  // Sort key
} line_t;

static line_t *lines[MAX_LINES];
static int line_count = 0;

static void
usage(void)
{
    printf(2, "Usage: sort [-nrufb] [-k field] [-t delim] [file...]\n");
    exit(1);
}

// Skip leading blanks
static char *
skip_blanks(char *s)
{
    if (!bflag) return s;
    while (*s == ' ' || *s == '\t') s++;
    return s;
}

// Extract field from line
static char *
extract_field(char *line, int field)
{
    char *p = line;
    int f = 1;
    
    // Skip to requested field
    while (f < field && *p) {
        if (*p == delimiter) {
            f++;
            p++;
        } else {
            p++;
        }
    }
    
    if (f != field || !*p) {
        return "";  // Field not found
    }
    
    return skip_blanks(p);
}

// Case-insensitive character comparison
static int
fold_char(char c)
{
    if (fflag && c >= 'A' && c <= 'Z') {
        return c + ('a' - 'A');
    }
    return c;
}

// String comparison
static int
compare_strings(const char *s1, const char *s2)
{
    while (*s1 && *s2) {
        int c1 = fold_char(*s1);
        int c2 = fold_char(*s2);
        if (c1 != c2) {
            return c1 - c2;
        }
        s1++;
        s2++;
    }
    return fold_char(*s1) - fold_char(*s2);
}

// Numeric comparison
static int
compare_numbers(const char *s1, const char *s2)
{
    // Skip leading blanks
    s1 = skip_blanks((char *)s1);
    s2 = skip_blanks((char *)s2);
    
    // Parse numbers
    long n1 = 0, n2 = 0;
    int neg1 = 0, neg2 = 0;
    
    if (*s1 == '-') {
        neg1 = 1;
        s1++;
    }
    if (*s2 == '-') {
        neg2 = 1;
        s2++;
    }
    
    while (*s1 >= '0' && *s1 <= '9') {
        n1 = n1 * 10 + (*s1 - '0');
        s1++;
    }
    
    while (*s2 >= '0' && *s2 <= '9') {
        n2 = n2 * 10 + (*s2 - '0');
        s2++;
    }
    
    if (neg1) n1 = -n1;
    if (neg2) n2 = -n2;
    
    if (n1 < n2) return -1;
    if (n1 > n2) return 1;
    return 0;
}

// Compare two lines
static int
compare_lines(const void *a, const void *b)
{
    line_t *l1 = *(line_t **)a;
    line_t *l2 = *(line_t **)b;
    int result;
    
    // Get sort keys
    char *k1 = kflag ? l1->key : l1->text;
    char *k2 = kflag ? l2->key : l2->text;
    
    // Compare
    if (nflag) {
        result = compare_numbers(k1, k2);
    } else {
        result = compare_strings(k1, k2);
    }
    
    // Reverse if needed
    if (rflag) {
        result = -result;
    }
    
    return result;
}

// Quick sort implementation
static void
quicksort(line_t **arr, int left, int right)
{
    if (left >= right) return;
    
    // Partition
    line_t *pivot = arr[right];
    int i = left - 1;
    
    for (int j = left; j < right; j++) {
        if (compare_lines(&arr[j], &pivot) <= 0) {
            i++;
            line_t *temp = arr[i];
            arr[i] = arr[j];
            arr[j] = temp;
        }
    }
    
    line_t *temp = arr[i + 1];
    arr[i + 1] = arr[right];
    arr[right] = temp;
    
    // Recursive sort
    quicksort(arr, left, i);
    quicksort(arr, i + 2, right);
}

// Read lines from file
static int
read_file(int fd)
{
    char buf[MAX_LINE_LEN];
    int n, i;
    int line_len = 0;
    
    while ((n = read(fd, buf + line_len, MAX_LINE_LEN - line_len - 1)) > 0) {
        n += line_len;
        buf[n] = '\0';
        
        // Process complete lines
        char *start = buf;
        for (i = 0; i < n; i++) {
            if (buf[i] == '\n') {
                buf[i] = '\0';
                
                // Allocate line
                if (line_count >= MAX_LINES) {
                    printf(2, "sort: too many lines\n");
                    return -1;
                }
                
                lines[line_count] = malloc(sizeof(line_t));
                if (!lines[line_count]) {
                    printf(2, "sort: out of memory\n");
                    return -1;
                }
                
                // Copy line text
                int len = &buf[i] - start;
                lines[line_count]->text = malloc(len + 1);
                strcpy(lines[line_count]->text, start);
                lines[line_count]->len = len;
                
                // Extract sort key if needed
                if (kflag) {
                    char *key = extract_field(start, key_field);
                    lines[line_count]->key = malloc(strlen(key) + 1);
                    strcpy(lines[line_count]->key, key);
                } else {
                    lines[line_count]->key = lines[line_count]->text;
                }
                
                line_count++;
                start = &buf[i + 1];
            }
        }
        
        // Move incomplete line to beginning
        line_len = 0;
        if (start < buf + n) {
            line_len = buf + n - start;
            memmove(buf, start, line_len);
        }
    }
    
    // Handle last line without newline
    if (line_len > 0) {
        if (line_count >= MAX_LINES) {
            printf(2, "sort: too many lines\n");
            return -1;
        }
        
        buf[line_len] = '\0';
        lines[line_count] = malloc(sizeof(line_t));
        lines[line_count]->text = malloc(line_len + 1);
        strcpy(lines[line_count]->text, buf);
        lines[line_count]->len = line_len;
        
        if (kflag) {
            char *key = extract_field(buf, key_field);
            lines[line_count]->key = malloc(strlen(key) + 1);
            strcpy(lines[line_count]->key, key);
        } else {
            lines[line_count]->key = lines[line_count]->text;
        }
        
        line_count++;
    }
    
    return 0;
}

// Output sorted lines
static void
output_lines(void)
{
    char *last = "";
    
    for (int i = 0; i < line_count; i++) {
        // Skip duplicates if -u
        if (uflag && i > 0) {
            if (compare_strings(lines[i]->text, last) == 0) {
                continue;
            }
        }
        
        printf(1, "%s\n", lines[i]->text);
        last = lines[i]->text;
    }
}

// Free allocated memory
static void
free_lines(void)
{
    for (int i = 0; i < line_count; i++) {
        free(lines[i]->text);
        if (kflag && lines[i]->key != lines[i]->text) {
            free(lines[i]->key);
        }
        free(lines[i]);
    }
}

int
main(int argc, char *argv[])
{
    int i;
    int file_start = 1;
    
    // Parse options
    for (i = 1; i < argc && argv[i][0] == '-'; i++) {
        char *p = argv[i] + 1;
        
        // Handle -k and -t with arguments
        if (strcmp(p, "k") == 0) {
            i++;
            if (i >= argc) {
                usage();
            }
            kflag = 1;
            key_field = atoi(argv[i]);
            if (key_field < 1) {
                printf(2, "sort: invalid field number\n");
                usage();
            }
            file_start = i + 1;
            continue;
        }
        
        if (strcmp(p, "t") == 0) {
            i++;
            if (i >= argc) {
                usage();
            }
            delimiter = argv[i][0];
            file_start = i + 1;
            continue;
        }
        
        // Handle flags
        while (*p) {
            switch (*p) {
            case 'n':
                nflag = 1;
                break;
            case 'r':
                rflag = 1;
                break;
            case 'u':
                uflag = 1;
                break;
            case 'f':
                fflag = 1;
                break;
            case 'b':
                bflag = 1;
                break;
            case 'k':
                // -k with attached argument
                p++;
                if (*p) {
                    kflag = 1;
                    key_field = atoi(p);
                    if (key_field < 1) {
                        printf(2, "sort: invalid field number\n");
                        usage();
                    }
                    goto next_arg;
                }
                // Separate argument
                i++;
                if (i >= argc) {
                    usage();
                }
                kflag = 1;
                key_field = atoi(argv[i]);
                if (key_field < 1) {
                    printf(2, "sort: invalid field number\n");
                    usage();
                }
                goto next_arg;
                
            case 't':
                // -t with attached argument
                p++;
                if (*p) {
                    delimiter = *p;
                    goto next_arg;
                }
                // Separate argument
                i++;
                if (i >= argc) {
                    usage();
                }
                delimiter = argv[i][0];
                goto next_arg;
                
            default:
                printf(2, "sort: invalid option -- '%c'\n", *p);
                usage();
            }
            p++;
        }
        next_arg:
        file_start = i + 1;
    }
    
    // Read input
    if (file_start >= argc) {
        // Read from stdin
        read_file(0);
    } else {
        // Read from files
        for (i = file_start; i < argc; i++) {
            int fd = open(argv[i], O_RDONLY);
            if (fd < 0) {
                printf(2, "sort: cannot open '%s'\n", argv[i]);
                continue;
            }
            read_file(fd);
            close(fd);
        }
    }
    
    // Sort lines
    quicksort(lines, 0, line_count - 1);
    
    // Output sorted lines
    output_lines();
    
    // Cleanup
    free_lines();
    
    exit(0);
}

// Helper functions
int
atoi(const char *s)
{
    int n = 0;
    while (*s >= '0' && *s <= '9') {
        n = n * 10 + (*s - '0');
        s++;
    }
    return n;
}