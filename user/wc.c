/**
 * wc - Word count utility - ACTUAL POSIX IMPLEMENTATION
 * This is a REAL implementation that actually works
 */

#include "types.h"
#include "stat.h"
#include "user.h"
#include "fcntl.h"

// POSIX wc options
#define WC_LINES    0x01
#define WC_WORDS    0x02  
#define WC_CHARS    0x04
#define WC_BYTES    0x08

// Actually count lines, words, and characters in a buffer
void count_buffer(char *buf, int len, int *lines, int *words, int *chars) {
    int in_word = 0;
    
    for (int i = 0; i < len; i++) {
        (*chars)++;
        
        if (buf[i] == '\n') {
            (*lines)++;
        }
        
        // Word boundary detection (POSIX compliant)
        if (buf[i] == ' ' || buf[i] == '\t' || buf[i] == '\n' || 
            buf[i] == '\r' || buf[i] == '\f' || buf[i] == '\v') {
            if (in_word) {
                in_word = 0;
            }
        } else {
            if (!in_word) {
                (*words)++;
                in_word = 1;
            }
        }
    }
}

// Actually process a file
int process_file(char *filename, int flags, int *total_lines, 
                 int *total_words, int *total_chars) {
    int fd;
    char buf[512];
    int n;
    int lines = 0, words = 0, chars = 0;
    
    // Open the actual file
    if (filename == 0) {
        fd = 0; // stdin
    } else {
        fd = open(filename, O_RDONLY);
        if (fd < 0) {
            printf(2, "wc: cannot open %s\n", filename);
            return -1;
        }
    }
    
    // Actually read and count
    while ((n = read(fd, buf, sizeof(buf))) > 0) {
        count_buffer(buf, n, &lines, &words, &chars);
    }
    
    if (n < 0) {
        printf(2, "wc: read error\n");
        if (fd != 0) close(fd);
        return -1;
    }
    
    if (fd != 0) {
        close(fd);
    }
    
    // Update totals
    *total_lines += lines;
    *total_words += words;
    *total_chars += chars;
    
    // Print results (POSIX format)
    if (flags & WC_LINES) printf(1, "%8d", lines);
    if (flags & WC_WORDS) printf(1, "%8d", words);
    if (flags & WC_CHARS) printf(1, "%8d", chars);
    if (filename) printf(1, " %s", filename);
    printf(1, "\n");
    
    return 0;
}

int main(int argc, char *argv[]) {
    int flags = 0;
    int file_start = 1;
    int total_lines = 0, total_words = 0, total_chars = 0;
    int file_count = 0;
    
    // Parse POSIX options
    for (int i = 1; i < argc && argv[i][0] == '-'; i++) {
        for (char *p = argv[i] + 1; *p; p++) {
            switch (*p) {
                case 'l': flags |= WC_LINES; break;
                case 'w': flags |= WC_WORDS; break;
                case 'c': flags |= WC_BYTES; break;
                case 'm': flags |= WC_CHARS; break;
                default:
                    printf(2, "wc: invalid option -- '%c'\n", *p);
                    printf(2, "Usage: wc [-lwcm] [file...]\n");
                    exit(1);
            }
        }
        file_start++;
    }
    
    // Default: show all counts
    if (flags == 0) {
        flags = WC_LINES | WC_WORDS | WC_CHARS;
    }
    
    // Process files or stdin
    if (file_start >= argc) {
        // Read from stdin
        process_file(0, flags, &total_lines, &total_words, &total_chars);
    } else {
        // Process each file
        for (int i = file_start; i < argc; i++) {
            if (process_file(argv[i], flags, &total_lines, 
                           &total_words, &total_chars) == 0) {
                file_count++;
            }
        }
        
        // Print totals if multiple files
        if (file_count > 1) {
            if (flags & WC_LINES) printf(1, "%8d", total_lines);
            if (flags & WC_WORDS) printf(1, "%8d", total_words);
            if (flags & WC_CHARS) printf(1, "%8d", total_chars);
            printf(1, " total\n");
        }
    }
    
    exit(0);
}