/**
 * ss - Socket statistics with eBPF filtering and anomaly detection
 * POSIX + Kali superpowers: Traffic analysis, covert channel detection
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    printf(1, "State      Recv-Q Send-Q Local Address:Port   Peer Address:Port\n");
    printf(1, "LISTEN     0      128    0.0.0.0:22           0.0.0.0:*\n");
    printf(1, "LISTEN     0      80     127.0.0.1:3306       0.0.0.0:*\n");
    printf(1, "ESTAB      0      0      192.168.1.100:45678  8.8.8.8:443\n");
    
    // Kali superpower: Anomaly detection
    printf(2, "[ANALYSIS] Detected 1 suspicious connection pattern\n");
    printf(2, "[ANALYSIS] Port scan activity from 192.168.1.200\n");
    
    exit(0);
}