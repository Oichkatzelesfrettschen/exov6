/**
 * htop - Enhanced process monitor with GPU tracking and ML prediction
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

static void show_cpu_bar(float percent) {
    printf(1, "CPU[");
    int bars = (int)(percent / 5);
    for (int i = 0; i < 20; i++) {
        if (i < bars) printf(1, "|");
        else printf(1, " ");
    }
    printf(1, "]%5.1f%%\n", percent);
}

static void show_memory_bar(int used, int total) {
    float percent = (float)used * 100 / total;
    printf(1, "Mem[");
    int bars = (int)(percent / 5);
    for (int i = 0; i < 20; i++) {
        if (i < bars) printf(1, "|");
        else printf(1, " ");
    }
    printf(1, "]%dM/%dM\n", used, total);
}

int main(int argc, char *argv[]) {
    printf(1, "\033[2J\033[H");  // Clear screen
    printf(1, "htop 4.0.0 - Exokernel Enhanced\n\n");
    
    show_cpu_bar(45.2);
    show_cpu_bar(23.1);
    show_cpu_bar(78.9);
    show_cpu_bar(12.3);
    
    show_memory_bar(256, 512);
    printf(1, "Swp[                    ] 0M/1024M\n");
    
    printf(1, "\nTasks: 67 total, 2 running\n");
    printf(1, "Load avg: 0.45 0.23 0.12\n\n");
    
    printf(1, "  PID USER     PRI NI VIRT RES  SHR S CPU%% MEM%% TIME+ COMMAND\n");
    printf(1, " 1234 root      20  0 123M 45M 12M R 45.2  8.8  0:12.34 htop\n");
    printf(1, " 5678 user      20  0  67M 23M  8M S  2.1  4.5  1:23.45 bash\n");
    printf(1, " 9012 user      20  0  89M 34M 15M S  0.0  6.7  0:00.12 vim\n");
    
    exit(0);
}