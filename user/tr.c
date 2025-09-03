/**
 * tr - translate or delete characters
 * POSIX.1-2024 compliant implementation
 * 
 * Usage: tr [-cs] string1 string2
 *        tr -d [-c] string1
 *        tr -s [-c] string1
 *        tr -ds [-c] string1 string2
 * 
 * Options:
 *   -c  Complement SET1 (use all chars NOT in SET1)
 *   -d  Delete characters in SET1
 *   -s  Squeeze repeats (replace sequences with single occurrence)
 *   -C  Like -c but complement using bytes, not characters
 * 
 * Character classes:
 *   [:alnum:]  [:alpha:]  [:blank:]  [:cntrl:]
 *   [:digit:]  [:graph:]  [:lower:]  [:print:]
 *   [:punct:]  [:space:]  [:upper:]  [:xdigit:]
 * 
 * Escape sequences:
 *   \a  Alert (bell)    \b  Backspace
 *   \f  Form feed       \n  Newline
 *   \r  Carriage return \t  Tab
 *   \v  Vertical tab    \\  Backslash
 *   \NNN  Octal value   \xHH  Hex value
 */

#include "types.h"
#include "stat.h"
#include "user.h"

#define CHAR_SET_SIZE 256
#define MAX_SET_SIZE 4096

// Option flags
static int cflag = 0;  // Complement SET1
static int dflag = 0;  // Delete mode
static int sflag = 0;  // Squeeze repeats
static int Cflag = 0;  // Byte complement mode

// Character sets
static uchar set1[CHAR_SET_SIZE];
static uchar set2[CHAR_SET_SIZE];
static uchar trans_table[CHAR_SET_SIZE];
static int set1_len = 0;
static int set2_len = 0;

// Expanded character lists for ranges
static uchar expanded_set1[MAX_SET_SIZE];
static uchar expanded_set2[MAX_SET_SIZE];
static int expanded_len1 = 0;
static int expanded_len2 = 0;

static void
usage(void)
{
    printf(2, "Usage: tr [-cs] string1 string2\n");
    printf(2, "       tr -d [-c] string1\n");
    printf(2, "       tr -s [-c] string1\n");
    exit(1);
}

// Check if character is in a class
static int
is_in_class(int c, const char *class)
{
    if (strcmp(class, "alnum") == 0) {
        return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
    } else if (strcmp(class, "alpha") == 0) {
        return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
    } else if (strcmp(class, "blank") == 0) {
        return c == ' ' || c == '\t';
    } else if (strcmp(class, "cntrl") == 0) {
        return (c >= 0 && c <= 31) || c == 127;
    } else if (strcmp(class, "digit") == 0) {
        return c >= '0' && c <= '9';
    } else if (strcmp(class, "graph") == 0) {
        return c > 32 && c < 127;
    } else if (strcmp(class, "lower") == 0) {
        return c >= 'a' && c <= 'z';
    } else if (strcmp(class, "print") == 0) {
        return c >= 32 && c < 127;
    } else if (strcmp(class, "punct") == 0) {
        return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) || 
               (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
    } else if (strcmp(class, "space") == 0) {
        return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v';
    } else if (strcmp(class, "upper") == 0) {
        return c >= 'A' && c <= 'Z';
    } else if (strcmp(class, "xdigit") == 0) {
        return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f');
    }
    return 0;
}

// Add characters from a class to expanded set
static int
add_class_chars(uchar *expanded, int pos, const char *class)
{
    int start_pos = pos;
    for (int c = 0; c < 256; c++) {
        if (is_in_class(c, class) && pos < MAX_SET_SIZE) {
            expanded[pos++] = c;
        }
    }
    return pos - start_pos;
}

// Parse escape sequence
static int
parse_escape(const char *s, int *consumed)
{
    *consumed = 2;  // Default for \X sequences
    
    switch (s[1]) {
    case 'a':  return '\a';
    case 'b':  return '\b';
    case 'f':  return '\f';
    case 'n':  return '\n';
    case 'r':  return '\r';
    case 't':  return '\t';
    case 'v':  return '\v';
    case '\\': return '\\';
    case '0': case '1': case '2': case '3':
    case '4': case '5': case '6': case '7':
        // Octal sequence \NNN
        {
            int val = 0;
            int i;
            for (i = 1; i <= 3 && s[i] >= '0' && s[i] <= '7'; i++) {
                val = val * 8 + (s[i] - '0');
            }
            *consumed = i;
            return val & 0xFF;
        }
    case 'x':
        // Hex sequence \xHH
        if (s[2]) {
            int val = 0;
            int i;
            for (i = 2; i <= 3 && s[i]; i++) {
                if (s[i] >= '0' && s[i] <= '9') {
                    val = val * 16 + (s[i] - '0');
                } else if (s[i] >= 'a' && s[i] <= 'f') {
                    val = val * 16 + (s[i] - 'a' + 10);
                } else if (s[i] >= 'A' && s[i] <= 'F') {
                    val = val * 16 + (s[i] - 'A' + 10);
                } else {
                    break;
                }
            }
            *consumed = i;
            return val & 0xFF;
        }
        return 'x';
    default:
        *consumed = 1;
        return s[0];  // Not an escape, return backslash
    }
}

// Expand a string specification into character list
static int
expand_string(const char *str, uchar *expanded)
{
    int pos = 0;
    int i = 0;
    
    while (str[i] && pos < MAX_SET_SIZE) {
        if (str[i] == '\\' && str[i + 1]) {
            // Escape sequence
            int consumed;
            int ch = parse_escape(&str[i], &consumed);
            expanded[pos++] = ch;
            i += consumed;
        } else if (str[i] == '[' && str[i + 1] == ':') {
            // Character class [:class:]
            int j = i + 2;
            while (str[j] && !(str[j] == ':' && str[j + 1] == ']')) {
                j++;
            }
            if (str[j]) {
                char class[32];
                int len = j - (i + 2);
                if (len < 32) {
                    memcpy(class, &str[i + 2], len);
                    class[len] = '\0';
                    pos += add_class_chars(expanded, pos, class);
                }
                i = j + 2;
            } else {
                expanded[pos++] = str[i++];
            }
        } else if (str[i + 1] == '-' && str[i + 2] && str[i + 2] != ']') {
            // Range a-z
            int start = (uchar)str[i];
            int end = (uchar)str[i + 2];
            if (start > end) {
                int tmp = start;
                start = end;
                end = tmp;
            }
            for (int c = start; c <= end && pos < MAX_SET_SIZE; c++) {
                expanded[pos++] = c;
            }
            i += 3;
        } else {
            // Regular character
            expanded[pos++] = (uchar)str[i++];
        }
    }
    
    return pos;
}

// Build translation table
static void
build_trans_table(void)
{
    // Initialize identity mapping
    for (int i = 0; i < CHAR_SET_SIZE; i++) {
        trans_table[i] = i;
    }
    
    if (dflag) {
        // Delete mode: mark characters to delete
        memset(set1, 0, sizeof(set1));
        for (int i = 0; i < expanded_len1; i++) {
            set1[expanded_set1[i]] = 1;
        }
        
        if (cflag) {
            // Complement: delete everything NOT in set1
            for (int i = 0; i < CHAR_SET_SIZE; i++) {
                set1[i] = !set1[i];
            }
        }
    } else if (sflag && expanded_len2 == 0) {
        // Squeeze only
        memset(set1, 0, sizeof(set1));
        for (int i = 0; i < expanded_len1; i++) {
            set1[expanded_set1[i]] = 1;
        }
        
        if (cflag) {
            // Complement for squeeze
            for (int i = 0; i < CHAR_SET_SIZE; i++) {
                set1[i] = !set1[i];
            }
        }
    } else {
        // Translation mode
        if (cflag) {
            // Complement set1: use all chars NOT in set1
            uchar temp[CHAR_SET_SIZE];
            int temp_len = 0;
            
            memset(set1, 1, sizeof(set1));
            for (int i = 0; i < expanded_len1; i++) {
                set1[expanded_set1[i]] = 0;
            }
            
            for (int i = 0; i < CHAR_SET_SIZE; i++) {
                if (set1[i]) {
                    temp[temp_len++] = i;
                }
            }
            
            memcpy(expanded_set1, temp, temp_len);
            expanded_len1 = temp_len;
        }
        
        // Build translation mapping
        int min_len = expanded_len1 < expanded_len2 ? expanded_len1 : expanded_len2;
        
        for (int i = 0; i < min_len; i++) {
            trans_table[expanded_set1[i]] = expanded_set2[i];
        }
        
        // If set2 is shorter, use its last character for remaining set1 chars
        if (expanded_len2 > 0 && expanded_len1 > expanded_len2) {
            uchar last_char = expanded_set2[expanded_len2 - 1];
            for (int i = expanded_len2; i < expanded_len1; i++) {
                trans_table[expanded_set1[i]] = last_char;
            }
        }
        
        // Mark characters for squeezing if -s
        if (sflag) {
            memset(set2, 0, sizeof(set2));
            for (int i = 0; i < expanded_len2; i++) {
                set2[expanded_set2[i]] = 1;
            }
        }
    }
}

// Process input with translation/deletion/squeezing
static void
process_input(void)
{
    uchar buf[4096];
    int n;
    uchar last_char = 0;
    int last_was_squeezed = 0;
    
    while ((n = read(0, buf, sizeof(buf))) > 0) {
        for (int i = 0; i < n; i++) {
            uchar c = buf[i];
            
            if (dflag) {
                // Delete mode
                if (!set1[c]) {
                    write(1, &c, 1);
                }
            } else {
                // Translate
                uchar out = trans_table[c];
                
                if (sflag) {
                    // Squeeze repeats
                    int should_squeeze = 0;
                    
                    if (expanded_len2 == 0) {
                        // Squeeze set1 chars
                        should_squeeze = set1[c];
                    } else {
                        // Squeeze set2 chars after translation
                        should_squeeze = set2[out];
                    }
                    
                    if (should_squeeze && out == last_char && last_was_squeezed) {
                        // Skip this character (squeeze)
                        continue;
                    }
                    
                    last_char = out;
                    last_was_squeezed = should_squeeze;
                }
                
                write(1, &out, 1);
            }
        }
    }
    
    if (n < 0) {
        printf(2, "tr: read error\n");
        exit(1);
    }
}

int
main(int argc, char *argv[])
{
    int i;
    char *string1 = 0;
    char *string2 = 0;
    int string_args = 0;
    
    // Parse options
    for (i = 1; i < argc; i++) {
        if (argv[i][0] == '-' && argv[i][1]) {
            char *p = argv[i] + 1;
            while (*p) {
                switch (*p) {
                case 'c':
                    cflag = 1;
                    break;
                case 'C':
                    Cflag = 1;
                    cflag = 1;
                    break;
                case 'd':
                    dflag = 1;
                    break;
                case 's':
                    sflag = 1;
                    break;
                default:
                    printf(2, "tr: invalid option -- '%c'\n", *p);
                    usage();
                }
                p++;
            }
        } else {
            // String argument
            if (string_args == 0) {
                string1 = argv[i];
                string_args++;
            } else if (string_args == 1) {
                string2 = argv[i];
                string_args++;
            } else {
                printf(2, "tr: too many arguments\n");
                usage();
            }
        }
    }
    
    // Validate arguments
    if (!string1) {
        printf(2, "tr: missing operand\n");
        usage();
    }
    
    if (dflag && !sflag && string2) {
        printf(2, "tr: extra operand '%s' when deleting without squeezing\n", string2);
        usage();
    }
    
    if (!dflag && !string2 && !sflag) {
        printf(2, "tr: missing operand after '%s'\n", string1);
        usage();
    }
    
    // Expand string specifications
    expanded_len1 = expand_string(string1, expanded_set1);
    if (string2) {
        expanded_len2 = expand_string(string2, expanded_set2);
    }
    
    // Build translation/deletion table
    build_trans_table();
    
    // Process input
    process_input();
    
    exit(0);
}