/**
 * @file stdio.h
 * @brief POSIX 2024 compliant stdio implementation
 * 
 * Complete implementation of stdio functions per POSIX.1-2024
 * with FeuerBird exokernel optimizations.
 */

#pragma once

#include <stddef.h>
#include <stdarg.h>
#include <stdint.h>

// =============================================================================
// POSIX 2024 STDIO CONSTANTS
// =============================================================================

#define POSIX_EOF           (-1)
#define POSIX_BUFSIZ        8192
#define POSIX_FILENAME_MAX  4096
#define POSIX_FOPEN_MAX     256
#define POSIX_TMP_MAX       238328

#define POSIX_L_tmpnam      20
#define POSIX_L_ctermid     9

// File modes
#define POSIX_IOFBF         0    // Full buffering
#define POSIX_IOLBF         1    // Line buffering  
#define POSIX_IONBF         2    // No buffering

// Standard streams
extern FILE *posix_stdin;
extern FILE *posix_stdout; 
extern FILE *posix_stderr;

// =============================================================================
// POSIX 2024 FILE STRUCTURE
// =============================================================================

typedef struct posix_file {
    int fd;                     // File descriptor
    int flags;                  // File flags
    int mode;                   // Buffering mode
    char *buffer;               // I/O buffer
    size_t buffer_size;         // Buffer size
    size_t buffer_pos;          // Current position in buffer
    size_t buffer_end;          // End of valid data in buffer
    int error;                  // Error indicator
    int eof;                    // EOF indicator
    struct posix_file *next;    // Linked list of open files
} FILE;

// =============================================================================
// FILE OPERATIONS
// =============================================================================

// File open/close
FILE *fopen(const char *filename, const char *mode);
FILE *fdopen(int fd, const char *mode);
FILE *freopen(const char *filename, const char *mode, FILE *stream);
int fclose(FILE *stream);
int fflush(FILE *stream);

// File positioning
int fseek(FILE *stream, long int offset, int whence);
long int ftell(FILE *stream);
void rewind(FILE *stream);
int fgetpos(FILE *stream, fpos_t *pos);
int fsetpos(FILE *stream, const fpos_t *pos);

// Error handling
void clearerr(FILE *stream);
int feof(FILE *stream);
int ferror(FILE *stream);
void perror(const char *s);

// =============================================================================
// CHARACTER I/O
// =============================================================================

// Character input
int fgetc(FILE *stream);
char *fgets(char *s, int size, FILE *stream);
int getc(FILE *stream);
int getchar(void);
int ungetc(int c, FILE *stream);

// Character output
int fputc(int c, FILE *stream);
int fputs(const char *s, FILE *stream);
int putc(int c, FILE *stream);
int putchar(int c);
int puts(const char *s);

// =============================================================================
// FORMATTED I/O
// =============================================================================

// Printf family
int printf(const char *format, ...);
int fprintf(FILE *stream, const char *format, ...);
int sprintf(char *str, const char *format, ...);
int snprintf(char *str, size_t size, const char *format, ...);

int vprintf(const char *format, va_list ap);
int vfprintf(FILE *stream, const char *format, va_list ap);
int vsprintf(char *str, const char *format, va_list ap);
int vsnprintf(char *str, size_t size, const char *format, va_list ap);

// Scanf family
int scanf(const char *format, ...);
int fscanf(FILE *stream, const char *format, ...);
int sscanf(const char *str, const char *format, ...);

int vscanf(const char *format, va_list ap);
int vfscanf(FILE *stream, const char *format, va_list ap);
int vsscanf(const char *str, const char *format, va_list ap);

// =============================================================================
// BINARY I/O
// =============================================================================

size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);

// =============================================================================
// FILE CONTROL
// =============================================================================

int setvbuf(FILE *stream, char *buffer, int mode, size_t size);
void setbuf(FILE *stream, char *buffer);

// =============================================================================
// TEMPORARY FILES
// =============================================================================

FILE *tmpfile(void);
char *tmpnam(char *s);
char *tempnam(const char *dir, const char *pfx);
int mkstemp(char *template);

// =============================================================================
// FILE SYSTEM OPERATIONS
// =============================================================================

int remove(const char *filename);
int rename(const char *old_filename, const char *new_filename);

// =============================================================================
// WIDE CHARACTER SUPPORT (POSIX 2024)
// =============================================================================

#include <wchar.h>

// Wide character file operations
wint_t fgetwc(FILE *stream);
wchar_t *fgetws(wchar_t *ws, int n, FILE *stream);
wint_t fputwc(wchar_t wc, FILE *stream);
int fputws(const wchar_t *ws, FILE *stream);
wint_t getwc(FILE *stream);
wint_t getwchar(void);
wint_t putwc(wchar_t wc, FILE *stream);
wint_t putwchar(wchar_t wc);
wint_t ungetwc(wint_t wc, FILE *stream);

// Wide character formatted I/O
int fwprintf(FILE *stream, const wchar_t *format, ...);
int swprintf(wchar_t *ws, size_t n, const wchar_t *format, ...);
int wprintf(const wchar_t *format, ...);

int fwscanf(FILE *stream, const wchar_t *format, ...);
int swscanf(const wchar_t *ws, const wchar_t *format, ...);
int wscanf(const wchar_t *format, ...);

int vfwprintf(FILE *stream, const wchar_t *format, va_list ap);
int vswprintf(wchar_t *ws, size_t n, const wchar_t *format, va_list ap);
int vwprintf(const wchar_t *format, va_list ap);

int vfwscanf(FILE *stream, const wchar_t *format, va_list ap);
int vswscanf(const wchar_t *ws, const wchar_t *format, va_list ap);
int vwscanf(const wchar_t *format, va_list ap);

// =============================================================================
// POSIX 2024 EXTENSIONS
// =============================================================================

// POSIX streams
FILE *open_memstream(char **ptr, size_t *sizeloc);
FILE *open_wmemstream(wchar_t **ptr, size_t *sizeloc);

// File locking
int flockfile(FILE *stream);
int ftrylockfile(FILE *stream);
void funlockfile(FILE *stream);

// Unlocked I/O (for performance)
int getc_unlocked(FILE *stream);
int getchar_unlocked(void);
int putc_unlocked(int c, FILE *stream);
int putchar_unlocked(int c);

// POSIX-specific functions
int fileno(FILE *stream);
FILE *popen(const char *command, const char *mode);
int pclose(FILE *stream);

// Threading support
int getw(FILE *stream);
int putw(int w, FILE *stream);

// =============================================================================
// INTERNAL IMPLEMENTATION DETAILS
// =============================================================================

// Buffer management
int posix_stdio_flush_buffer(FILE *stream);
int posix_stdio_fill_buffer(FILE *stream);
int posix_stdio_allocate_buffer(FILE *stream);
void posix_stdio_free_buffer(FILE *stream);

// File registry
void posix_stdio_register_file(FILE *stream);
void posix_stdio_unregister_file(FILE *stream);
void posix_stdio_flush_all(void);

// Initialization
void posix_stdio_init(void);
void posix_stdio_cleanup(void);

#endif // POSIX2024_STDIO_H