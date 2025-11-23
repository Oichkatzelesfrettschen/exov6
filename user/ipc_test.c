/**
 * @file ipc_test.c
 * @brief IPC Infrastructure Test (Phase 9)
 *
 * This test validates the IPC system:
 *   1. Mailbox initialization
 *   2. Send/receive semantics
 *   3. Blocking behavior
 *
 * For a full ping-pong test, we need fork() which requires Phase 10.
 * This test validates the basic infrastructure.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// LibOS functions
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);
extern void scheduler_init(void);
extern int thread_create(void (*entry)(void*), void *arg, const char *name);
extern void thread_yield(void);

// IPC functions
extern int sys_ipc_send(int target_pid, uint64 w0, uint64 w1, uint64 w2);
extern int sys_ipc_recv(int *sender_pid, uint64 *w0, uint64 *w1, uint64 *w2);

// Our PID (we'll discover it via IPC)
static volatile int my_pid = 0;
static volatile int receiver_ready = 0;
static volatile int test_passed = 0;

// Test values
#define MAGIC_W0  0xDEADBEEF
#define MAGIC_W1  0xCAFEBABE
#define MAGIC_W2  0x12345678

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
 * Receiver thread - waits for messages
 */
void receiver_thread(void *arg) {
    (void)arg;

    print("[RECEIVER] Thread started, waiting for message...\n");
    receiver_ready = 1;

    int sender_pid = 0;
    uint64 w0 = 0, w1 = 0, w2 = 0;

    // This will block until message arrives
    int result = sys_ipc_recv(&sender_pid, &w0, &w1, &w2);

    if (result < 0) {
        print("[RECEIVER] ERROR: sys_ipc_recv failed!\n");
        return;
    }

    print("[RECEIVER] Message received!\n");
    print("    Sender PID: ");
    print_uint(sender_pid);
    print("\n    w0: ");
    print_hex(w0);
    print("\n    w1: ");
    print_hex(w1);
    print("\n    w2: ");
    print_hex(w2);
    print("\n");

    // Verify values
    if (w0 == MAGIC_W0 && w1 == MAGIC_W1 && w2 == MAGIC_W2) {
        print("[RECEIVER] Values CORRECT!\n");
        test_passed = 1;
    } else {
        print("[RECEIVER] Values INCORRECT!\n");
    }

    // Remember our PID from the sender
    my_pid = sender_pid;
}

/**
 * Sender thread - sends a message
 */
void sender_thread(void *arg) {
    int target_pid = *(int*)arg;

    print("[SENDER] Thread started, target PID: ");
    print_uint(target_pid);
    print("\n");

    // Wait for receiver to be ready
    while (!receiver_ready) {
        thread_yield();
    }

    print("[SENDER] Sending message...\n");
    print("    w0: ");
    print_hex(MAGIC_W0);
    print("\n    w1: ");
    print_hex(MAGIC_W1);
    print("\n    w2: ");
    print_hex(MAGIC_W2);
    print("\n");

    int result = sys_ipc_send(target_pid, MAGIC_W0, MAGIC_W1, MAGIC_W2);

    if (result < 0) {
        print("[SENDER] ERROR: sys_ipc_send failed (code ");
        print_uint(-result);
        print(")\n");
    } else {
        print("[SENDER] Message sent successfully!\n");
    }
}

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  IPC_TEST: Inter-Process Communication (Phase 9)\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    // Initialize exception handling
    print("[1/4] Initializing exception handling...\n");
    libos_exception_init();

    // Initialize scheduler
    print("[2/4] Initializing scheduler...\n");
    scheduler_init();

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  INTRA-PROCESS IPC TEST\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("This test uses threads within a single process to validate\n");
    print("the IPC infrastructure. Full inter-process IPC requires the\n");
    print("File Server (Phase 9.5) and process spawning (Phase 10).\n");
    print("\n");

    // Get our PID (we'll use 1 as a placeholder)
    // In a real test, we'd get this from the kernel
    int our_pid = 1;  // Assume we're PID 1

    print("[3/4] Creating receiver thread...\n");
    int recv_tid = thread_create(receiver_thread, 0, "receiver");
    if (recv_tid < 0) {
        print("ERROR: Failed to create receiver thread!\n");
        goto halt;
    }

    print("[4/4] Creating sender thread with target PID ");
    print_uint(our_pid);
    print("...\n");
    int send_tid = thread_create(sender_thread, &our_pid, "sender");
    if (send_tid < 0) {
        print("ERROR: Failed to create sender thread!\n");
        goto halt;
    }

    print("\n");
    print("Yielding to threads...\n");
    print("\n");

    // Wait for test to complete
    int timeout = 1000000;
    while (!test_passed && --timeout > 0) {
        thread_yield();
    }

    print("\n");
    if (test_passed) {
        print("═══════════════════════════════════════════════════════════\n");
        print("  TEST PASSED: IPC Infrastructure Working!\n");
        print("═══════════════════════════════════════════════════════════\n");
        print("\n");
        print("The IPC system successfully:\n");
        print("  1. Initialized per-process mailbox\n");
        print("  2. Blocked receiver until message arrived\n");
        print("  3. Delivered message with correct values\n");
        print("  4. Woke receiver after send\n");
        print("\n");
    } else {
        print("═══════════════════════════════════════════════════════════\n");
        print("  TEST FAILED or TIMEOUT\n");
        print("═══════════════════════════════════════════════════════════\n");
    }

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
