/**
 * @file test_illumos_binary.c
 * @brief Illumos/Solaris test binary with Illumos-specific syscalls
 * 
 * Compile on Illumos: gcc -o test_illumos test_illumos_binary.c -lcontract -ldoor
 * This creates an Illumos ELF with Solaris ABI note
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <zone.h>
#include <door.h>
#include <thread.h>
#include <sys/lwp.h>
#include <sys/contract.h>
#include <sys/ctfs.h>
#include <libcontract.h>
#include <sys/processor.h>
#include <sys/pset.h>

// Illumos-specific syscall numbers
#define SYS_zone        227
#define SYS_door_create 180
#define SYS_door_call   181
#define SYS_lwp_create  159
#define SYS_lwp_self    160
#define SYS_lwp_info    161
#define SYS_pset_create 284
#define SYS_pset_bind   285

// Test zone operations
int test_illumos_zones(void) {
    printf("Testing Illumos zone syscalls...\n");
    
    // Get current zone ID
    zoneid_t zid = getzoneid();
    printf("  ✓ Current zone ID: %d\n", zid);
    
    // Get zone name
    char zonename[ZONENAME_MAX];
    if (getzonenamebyid(zid, zonename, sizeof(zonename)) >= 0) {
        printf("  ✓ Zone name: %s\n", zonename);
    } else {
        printf("  ✗ Cannot get zone name: %s\n", strerror(errno));
    }
    
    // Check if in global zone
    if (zid == GLOBAL_ZONEID) {
        printf("  ✓ Running in global zone\n");
    } else {
        printf("  ✓ Running in non-global zone %d\n", zid);
    }
    
    // List available zones (if permitted)
    zoneid_t zones[256];
    uint_t nzones = sizeof(zones) / sizeof(zones[0]);
    
    if (zone_list(zones, &nzones) == 0) {
        printf("  ✓ System has %u zones\n", nzones);
    } else {
        printf("  ✓ Cannot list zones (permission denied)\n");
    }
    
    return 0;
}

// Door server procedure
static void door_server_proc(void *cookie, char *argp, size_t arg_size,
                             door_desc_t *dp, uint_t n_desc) {
    char response[] = "Door response";
    door_return(response, sizeof(response), NULL, 0);
}

// Test door IPC
int test_illumos_doors(void) {
    printf("Testing Illumos door IPC...\n");
    
    // Create a door
    int door_fd = door_create(door_server_proc, NULL, 0);
    if (door_fd < 0) {
        printf("  ✗ door_create failed: %s\n", strerror(errno));
        return -1;
    }
    printf("  ✓ Door created with fd %d\n", door_fd);
    
    // Attach door to filesystem
    const char *door_path = "/tmp/test_door";
    unlink(door_path);  // Remove if exists
    
    int fd = open(door_path, O_CREAT | O_RDWR, 0644);
    if (fd >= 0) {
        close(fd);
        
        if (fattach(door_fd, door_path) == 0) {
            printf("  ✓ Door attached to %s\n", door_path);
            
            // Test door call
            int client_fd = open(door_path, O_RDONLY);
            if (client_fd >= 0) {
                door_arg_t arg;
                char buf[256] = "Door request";
                char rbuf[256];
                
                arg.data_ptr = buf;
                arg.data_size = strlen(buf) + 1;
                arg.desc_ptr = NULL;
                arg.desc_num = 0;
                arg.rbuf = rbuf;
                arg.rsize = sizeof(rbuf);
                
                if (door_call(client_fd, &arg) == 0) {
                    printf("  ✓ Door call succeeded: %s\n", (char *)arg.rbuf);
                } else {
                    printf("  ✗ Door call failed: %s\n", strerror(errno));
                }
                
                close(client_fd);
            }
            
            fdetach(door_path);
        } else {
            printf("  ✗ fattach failed: %s\n", strerror(errno));
        }
    }
    
    close(door_fd);
    unlink(door_path);
    return 0;
}

// Test LWP (Light Weight Process) operations
int test_illumos_lwp(void) {
    printf("Testing Illumos LWP syscalls...\n");
    
    // Get current LWP ID
    lwpid_t lwpid = _lwp_self();
    printf("  ✓ Current LWP ID: %d\n", lwpid);
    
    // Get LWP info
    struct lwpinfo {
        lwpid_t lwp_id;
        int lwp_errno;
        int lwp_cursig;
    } info;
    
    if (_lwp_info(&info) == 0) {
        printf("  ✓ LWP info retrieved\n");
    } else {
        printf("  ✓ _lwp_info not available\n");
    }
    
    // Count LWPs
    int nlwps = 0;
    lwpid_t *lwps = NULL;
    if (_lwp_enum(&lwps, &nlwps) == 0) {
        printf("  ✓ Process has %d LWPs\n", nlwps);
        free(lwps);
    } else {
        printf("  ✓ Cannot enumerate LWPs\n");
    }
    
    return 0;
}

// Test processor sets
int test_illumos_psets(void) {
    printf("Testing Illumos processor sets...\n");
    
    // Get number of processors
    int nprocs = sysconf(_SC_NPROCESSORS_ONLN);
    printf("  ✓ System has %d online processors\n", nprocs);
    
    // Try to create a processor set (requires privileges)
    psetid_t pset;
    if (pset_create(&pset) == 0) {
        printf("  ✓ Created processor set %d\n", pset);
        
        // Get info about the set
        uint_t type;
        if (pset_info(pset, &type, NULL, NULL) == 0) {
            printf("  ✓ Processor set type: %u\n", type);
        }
        
        // Destroy the set
        pset_destroy(pset);
    } else {
        printf("  ✓ Cannot create processor set (need privileges)\n");
    }
    
    // Get current processor set binding
    psetid_t current_pset;
    if (pset_bind(PS_QUERY, P_PID, getpid(), &current_pset) == 0) {
        if (current_pset == PS_NONE) {
            printf("  ✓ Process not bound to any processor set\n");
        } else {
            printf("  ✓ Process bound to processor set %d\n", current_pset);
        }
    }
    
    return 0;
}

// Test contract filesystem
int test_illumos_contracts(void) {
    printf("Testing Illumos contract filesystem...\n");
    
    // Check if contract filesystem is mounted
    struct stat st;
    if (stat(CTFS_ROOT, &st) == 0) {
        printf("  ✓ Contract filesystem mounted at %s\n", CTFS_ROOT);
        
        // Try to open process contract template
        int tmpl_fd = open(CTFS_ROOT "/process/template", O_RDWR);
        if (tmpl_fd >= 0) {
            printf("  ✓ Opened process contract template\n");
            
            // Set contract terms
            if (ct_pr_tmpl_set_fatal(tmpl_fd, CT_PR_EV_HWERR) == 0) {
                printf("  ✓ Set contract fatal events\n");
            }
            
            close(tmpl_fd);
        } else {
            printf("  ✗ Cannot open contract template: %s\n", strerror(errno));
        }
    } else {
        printf("  ✓ Contract filesystem not available\n");
    }
    
    return 0;
}

// Test /dev/poll (Illumos-specific poll mechanism)
int test_illumos_devpoll(void) {
    printf("Testing Illumos /dev/poll...\n");
    
    int dpfd = open("/dev/poll", O_RDWR);
    if (dpfd < 0) {
        printf("  ✓ /dev/poll not available\n");
        return 0;
    }
    
    printf("  ✓ Opened /dev/poll with fd %d\n", dpfd);
    
    // Create a pipe for testing
    int pipefd[2];
    if (pipe(pipefd) == 0) {
        // Register pipe for polling
        struct pollfd pfd = {
            .fd = pipefd[0],
            .events = POLLIN,
            .revents = 0
        };
        
        if (write(dpfd, &pfd, sizeof(pfd)) == sizeof(pfd)) {
            printf("  ✓ Registered fd with /dev/poll\n");
            
            // Write to pipe
            write(pipefd[1], "test", 4);
            
            // Poll for events
            struct dvpoll dp = {
                .dp_timeout = 100,  // 100ms
                .dp_nfds = 1,
                .dp_fds = &pfd
            };
            
            if (ioctl(dpfd, DP_POLL, &dp) >= 0) {
                printf("  ✓ /dev/poll returned events\n");
            }
        }
        
        close(pipefd[0]);
        close(pipefd[1]);
    }
    
    close(dpfd);
    return 0;
}

int main(int argc, char *argv[]) {
    printf("===========================================\n");
    printf("Illumos Personality Test Binary\n");
    printf("===========================================\n");
    printf("This binary uses Illumos-specific syscalls\n");
    printf("and should be detected as PERSONALITY_ILLUMOS\n");
    printf("===========================================\n\n");
    
    // Show basic info
    printf("Process ID: %d\n", getpid());
    printf("User ID: %d\n", getuid());
    printf("Group ID: %d\n", getgid());
    printf("\n");
    
    // Run Illumos-specific tests
    int failures = 0;
    
    if (test_illumos_zones() < 0) failures++;
    printf("\n");
    
    if (test_illumos_doors() < 0) failures++;
    printf("\n");
    
    if (test_illumos_lwp() < 0) failures++;
    printf("\n");
    
    if (test_illumos_psets() < 0) failures++;
    printf("\n");
    
    if (test_illumos_contracts() < 0) failures++;
    printf("\n");
    
    if (test_illumos_devpoll() < 0) failures++;
    printf("\n");
    
    // Summary
    printf("===========================================\n");
    if (failures == 0) {
        printf("✅ All Illumos personality tests passed!\n");
    } else {
        printf("❌ %d Illumos personality tests failed\n", failures);
    }
    printf("===========================================\n");
    
    return failures;
}