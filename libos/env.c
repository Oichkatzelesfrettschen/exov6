#include <string.h>
#include <stdlib.h>
#include "libos/posix.h"

#ifndef LIBOS_MAXENV
#define LIBOS_MAXENV 32
#endif

struct env_entry {
    char *name;
    char *value;
};

static struct env_entry env_table[LIBOS_MAXENV];

int libos_setenv(const char *name, const char *value) {
    if(!name || !value)
        return -1;
    for(int i = 0; i < LIBOS_MAXENV; i++) {
        if(env_table[i].name && strcmp(env_table[i].name, name) == 0) {
            char *v = strdup(value);
            if(!v)
                return -1;
            free(env_table[i].value);
            env_table[i].value = v;
            return 0;
        }
    }
    for(int i = 0; i < LIBOS_MAXENV; i++) {
        if(!env_table[i].name) {
            env_table[i].name = strdup(name);
            env_table[i].value = strdup(value);
            if(!env_table[i].name || !env_table[i].value) {
                free(env_table[i].name);
                free(env_table[i].value);
                env_table[i].name = env_table[i].value = NULL;
                return -1;
            }
            return 0;
        }
    }
    return -1;
}

const char *libos_getenv(const char *name) {
    if(!name)
        return NULL;
    for(int i = 0; i < LIBOS_MAXENV; i++) {
        if(env_table[i].name && strcmp(env_table[i].name, name) == 0)
            return env_table[i].value;
    }
    return NULL;
}
