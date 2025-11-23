/**
 * @file fs_client_test.c
 * @brief File Server Client Test (Phase 9.5)
 *
 * This test demonstrates the client-server file system architecture.
 * It sends IPC messages to the file server (fs_srv) and receives responses.
 *
 * Note: This test assumes fs_srv is running as PID 2.
 * In a full system, init would spawn fs_srv before running this test.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>
#include <fs_protocol.h>

// LibOS
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);
extern void scheduler_init(void);
extern void thread_yield(void);

// IPC
extern int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2);
extern int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2);

static void print_uint(uint32_t n) {
    if (n == 0) { print("0"); return; }
    char buf[12];
    int i = 0;
    while (n > 0) { buf[i++] = '0' + (n % 10); n /= 10; }
    char out[12];
    for (int j = 0; j < i; j++) out[j] = buf[i - 1 - j];
    out[i] = '\0';
    print(out);
}

/**
 * Send request to file server and wait for response
 */
static int fs_call(int req_type, uint64 arg1, uint64 arg2,
                   uint64 *resp1, uint64 *resp2) {
    // Send request
    if (sys_ipc_send(FS_SERVER_PID, req_type, arg1, arg2) < 0) {
        print("[CLIENT] Failed to send request!\n");
        return -1;
    }

    // Wait for response
    int server_pid;
    uint64 r0, r1, r2;
    if (sys_ipc_recv(&server_pid, &r0, &r1, &r2) < 0) {
        print("[CLIENT] Failed to receive response!\n");
        return -1;
    }

    if (server_pid != FS_SERVER_PID) {
        print("[CLIENT] Response from wrong PID!\n");
        return -1;
    }

    if (resp1) *resp1 = r1;
    if (resp2) *resp2 = r2;

    return (int)r0;  // Result code
}

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  FS_CLIENT_TEST: File Server Client (Phase 9.5)\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    // Initialize
    print("[1/2] Initializing exception handling...\n");
    libos_exception_init();

    print("[2/2] Initializing scheduler...\n");
    scheduler_init();

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  TESTING FILE SERVER COMMUNICATION\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    // Test 1: Ping
    print("[TEST 1] Sending PING to file server (PID ");
    print_uint(FS_SERVER_PID);
    print(")...\n");

    uint64 pong_val = 0;
    int result = fs_call(FS_REQ_PING, 0, 0, &pong_val, 0);

    if (result == FS_OK) {
        print("    PONG received! Value: ");
        print_hex(pong_val);
        print("\n");
    } else {
        print("    PING failed! Result: ");
        print_uint(-result);
        print("\n");
        print("\n    NOTE: Make sure fs_srv is running as PID 2!\n");
        goto halt;
    }

    // Test 2: Open root directory
    print("\n[TEST 2] Opening root directory...\n");

    int fd = fs_call(FS_REQ_OPEN, 0, FS_O_RDONLY, 0, 0);

    if (fd >= 0) {
        print("    Root directory opened as fd ");
        print_uint(fd);
        print("\n");
    } else {
        print("    OPEN failed! Error: ");
        print_uint(-fd);
        print("\n");
        goto halt;
    }

    // Test 3: Stat the file
    print("\n[TEST 3] Getting file status...\n");

    uint64 type, size;
    result = fs_call(FS_REQ_STAT, fd, 0, &type, &size);

    if (result == FS_OK) {
        print("    Type: ");
        switch ((int)type) {
            case 1: print("DIR"); break;
            case 2: print("FILE"); break;
            case 3: print("DEV"); break;
            default: print_uint((uint32_t)type); break;
        }
        print("\n    Size: ");
        print_uint((uint32_t)size);
        print(" bytes\n");
    } else {
        print("    STAT failed! Error: ");
        print_uint(-result);
        print("\n");
    }

    // Test 4: Read directory entries
    print("\n[TEST 4] Reading directory entries...\n");

    for (int i = 0; i < 10; i++) {
        uint64 inum, name_char;
        result = fs_call(FS_REQ_READDIR, fd, i, &inum, &name_char);

        if (result == 0) {
            // End of directory
            print("    (end of directory)\n");
            break;
        } else if (result > 0) {
            print("    Entry ");
            print_uint(i);
            print(": inode ");
            print_uint((uint32_t)inum);
            print("\n");
        } else {
            print("    READDIR error: ");
            print_uint(-result);
            print("\n");
            break;
        }
    }

    // Test 5: Close file
    print("\n[TEST 5] Closing file...\n");

    result = fs_call(FS_REQ_CLOSE, fd, 0, 0, 0);

    if (result == FS_OK) {
        print("    File closed.\n");
    } else {
        print("    CLOSE failed! Error: ");
        print_uint(-result);
        print("\n");
    }

    // Success!
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  PHASE 9.5 COMPLETE: CLIENT-SERVER FILE SYSTEM\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("The Great Schism is complete!\n");
    print("  - File Server owns VirtIO hardware exclusively\n");
    print("  - Client communicates via IPC messages\n");
    print("  - NO direct hardware access from client\n");
    print("\n");
    print("This is the microkernel/exokernel architecture:\n");
    print("  Client → IPC → Server → Hardware\n");
    print("\n");

halt:
    while (1) {
#if defined(__x86_64__)
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");
#else
        __asm__ volatile("" ::: "memory");
#endif
    }

    return 0;
}
