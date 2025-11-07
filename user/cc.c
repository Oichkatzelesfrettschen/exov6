/*
 * cc - C Compiler Wrapper for ExoV6
 * 
 * Provides a standard 'cc' interface that delegates to the appropriate
 * compiler (gcc or clang) with correct flags for exokernel environment.
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

#define MAXARGS 64

static char *compiler_path = "/usr/bin/gcc";  /* Default compiler */
static char *default_includes[] = {
    "-I/usr/include",
    "-I/usr/include/exov6",
    "-I/usr/local/include",
    0
};

static char *default_libs[] = {
    "-L/usr/lib",
    "-L/usr/local/lib",
    0
};

int main(int argc, char *argv[]) {
    char *args[MAXARGS];
    int nargs = 0;
    int i;
    int add_defaults = 1;
    
    /* Start with compiler */
    args[nargs++] = compiler_path;
    
    /* Add default includes unless -nostdinc specified */
    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-nostdinc") == 0) {
            add_defaults = 0;
            break;
        }
    }
    
    if (add_defaults) {
        for (i = 0; default_includes[i] && nargs < MAXARGS - 1; i++) {
            args[nargs++] = default_includes[i];
        }
    }
    
    /* Add user arguments */
    for (i = 1; i < argc && nargs < MAXARGS - 1; i++) {
        args[nargs++] = argv[i];
    }
    
    /* Add default library paths if linking */
    int is_linking = 1;
    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-c") == 0 || strcmp(argv[i], "-E") == 0 || 
            strcmp(argv[i], "-S") == 0) {
            is_linking = 0;
            break;
        }
    }
    
    if (is_linking && add_defaults) {
        for (i = 0; default_libs[i] && nargs < MAXARGS - 1; i++) {
            args[nargs++] = default_libs[i];
        }
    }
    
    args[nargs] = 0;
    
    /* Execute compiler */
    exec(compiler_path, args);
    
    /* If exec fails, try clang */
    compiler_path = "/usr/bin/clang";
    args[0] = compiler_path;
    exec(compiler_path, args);
    
    printf(2, "cc: compiler not found\n");
    exit(1);
    return 1;
}
