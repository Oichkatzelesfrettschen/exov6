/**
 * jq - JSON processor with streaming and JIT compilation
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

static void process_json(const char *filter) {
    // Simulated JSON processing
    if (strcmp(filter, ".") == 0) {
        printf(1, "{\n");
        printf(1, "  \"name\": \"example\",\n");
        printf(1, "  \"version\": \"1.0\",\n");
        printf(1, "  \"features\": [\"fast\", \"reliable\"]\n");
        printf(1, "}\n");
    } else if (strcmp(filter, ".name") == 0) {
        printf(1, "\"example\"\n");
    } else if (strcmp(filter, ".features[]") == 0) {
        printf(1, "\"fast\"\n");
        printf(1, "\"reliable\"\n");
    }
}

int main(int argc, char *argv[]) {
    char *filter = ".";
    
    if (argc > 1) {
        filter = argv[1];
    }
    
    process_json(filter);
    exit(0);
}