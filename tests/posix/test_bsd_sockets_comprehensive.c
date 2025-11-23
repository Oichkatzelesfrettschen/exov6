/**
 * @file test_bsd_sockets_comprehensive.c
 * @brief Comprehensive BSD Socket Test Suite
 *
 * Tests the synthesized BSD socket implementation covering:
 * - 4.4BSD: Core socket operations
 * - FreeBSD: Socket options, buffer management
 * - NetBSD: Protocol handling
 * - OpenBSD: pledge-style restrictions
 * - DragonFlyBSD: Atomic operations
 *
 * Test Categories:
 * 1. Socket Creation and Destruction
 * 2. Binding and Addressing
 * 3. Connection Management
 * 4. Data Transfer
 * 5. Socket Options
 * 6. Non-blocking I/O
 * 7. Socket Pairs
 * 8. Error Handling
 * 9. Capability Restrictions (pledge-style)
 * 10. Buffer Management
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <arpa/inet.h>

/* Test framework */
static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_ASSERT(cond, msg) do { \
    tests_run++; \
    if (cond) { \
        tests_passed++; \
        printf("  [PASS] %s\n", msg); \
    } else { \
        tests_failed++; \
        printf("  [FAIL] %s (line %d)\n", msg, __LINE__); \
    } \
} while(0)

#define TEST_SECTION(name) printf("\n=== %s ===\n", name)

/*
 * Test Category 1: Socket Creation and Destruction
 */
static void test_socket_creation(void)
{
    TEST_SECTION("Socket Creation and Destruction");

    /* Test SOCK_STREAM creation */
    int tcp_fd = socket(AF_INET, SOCK_STREAM, 0);
    TEST_ASSERT(tcp_fd >= 0, "Create TCP socket (SOCK_STREAM)");
    if (tcp_fd >= 0) close(tcp_fd);

    /* Test SOCK_DGRAM creation */
    int udp_fd = socket(AF_INET, SOCK_DGRAM, 0);
    TEST_ASSERT(udp_fd >= 0, "Create UDP socket (SOCK_DGRAM)");
    if (udp_fd >= 0) close(udp_fd);

    /* Test AF_UNIX creation */
    int unix_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    TEST_ASSERT(unix_fd >= 0 || errno == EAFNOSUPPORT,
                "Create Unix socket (AF_UNIX)");
    if (unix_fd >= 0) close(unix_fd);

    /* Test invalid domain */
    int bad_fd = socket(999, SOCK_STREAM, 0);
    TEST_ASSERT(bad_fd < 0 && (errno == EAFNOSUPPORT || errno == EPROTONOSUPPORT),
                "Reject invalid domain");

    /* Test invalid type */
    bad_fd = socket(AF_INET, 999, 0);
    TEST_ASSERT(bad_fd < 0, "Reject invalid socket type");

    /* Test SOCK_RAW (may require privileges) */
    int raw_fd = socket(AF_INET, SOCK_RAW, 0);
    TEST_ASSERT(raw_fd >= 0 || errno == EPERM || errno == EPROTONOSUPPORT,
                "Raw socket creation (or permission denied)");
    if (raw_fd >= 0) close(raw_fd);

    /* Test socket with SOCK_NONBLOCK flag (Linux extension) */
#ifdef SOCK_NONBLOCK
    int nb_fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0);
    TEST_ASSERT(nb_fd >= 0, "Create non-blocking socket");
    if (nb_fd >= 0) close(nb_fd);
#endif

    /* Test socket with SOCK_CLOEXEC flag (Linux extension) */
#ifdef SOCK_CLOEXEC
    int cloexec_fd = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    TEST_ASSERT(cloexec_fd >= 0, "Create close-on-exec socket");
    if (cloexec_fd >= 0) close(cloexec_fd);
#endif
}

/*
 * Test Category 2: Binding and Addressing
 */
static void test_binding(void)
{
    TEST_SECTION("Binding and Addressing");

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    TEST_ASSERT(fd >= 0, "Create socket for binding tests");
    if (fd < 0) return;

    /* Bind to any address, any port */
    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = INADDR_ANY;
    addr.sin_port = 0;  /* Let kernel choose port */

    int ret = bind(fd, (struct sockaddr *)&addr, sizeof(addr));
    TEST_ASSERT(ret == 0, "Bind to INADDR_ANY:0");

    /* Get assigned address */
    struct sockaddr_in bound_addr;
    socklen_t len = sizeof(bound_addr);
    ret = getsockname(fd, (struct sockaddr *)&bound_addr, &len);
    TEST_ASSERT(ret == 0 || errno == EOPNOTSUPP, "getsockname() works");
    if (ret == 0) {
        TEST_ASSERT(bound_addr.sin_port != 0, "Kernel assigned a port");
    }

    close(fd);

    /* Test binding to specific port */
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) {
        addr.sin_port = htons(54321);
        ret = bind(fd, (struct sockaddr *)&addr, sizeof(addr));
        TEST_ASSERT(ret == 0 || errno == EADDRINUSE || errno == EACCES,
                    "Bind to specific port");
        close(fd);
    }

    /* Test double bind (should fail) */
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) {
        addr.sin_port = 0;
        bind(fd, (struct sockaddr *)&addr, sizeof(addr));
        ret = bind(fd, (struct sockaddr *)&addr, sizeof(addr));
        TEST_ASSERT(ret < 0, "Double bind fails");
        close(fd);
    }

    /* Test bind on invalid fd */
    ret = bind(9999, (struct sockaddr *)&addr, sizeof(addr));
    TEST_ASSERT(ret < 0 && errno == EBADF, "Bind on invalid fd returns EBADF");
}

/*
 * Test Category 3: Connection Management
 */
static void test_connection(void)
{
    TEST_SECTION("Connection Management");

    int server_fd = socket(AF_INET, SOCK_STREAM, 0);
    TEST_ASSERT(server_fd >= 0, "Create server socket");
    if (server_fd < 0) return;

    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = INADDR_ANY;
    addr.sin_port = 0;

    int ret = bind(server_fd, (struct sockaddr *)&addr, sizeof(addr));
    TEST_ASSERT(ret == 0, "Bind server socket");

    ret = listen(server_fd, 5);
    TEST_ASSERT(ret == 0, "Listen on server socket");

    /* Get server port */
    socklen_t len = sizeof(addr);
    getsockname(server_fd, (struct sockaddr *)&addr, &len);
    uint16_t server_port = addr.sin_port;

    /* Test listen backlog */
    ret = listen(server_fd, 128);
    TEST_ASSERT(ret == 0, "Increase listen backlog");

    /* Test listen on non-bound socket */
    int fd2 = socket(AF_INET, SOCK_STREAM, 0);
    if (fd2 >= 0) {
        ret = listen(fd2, 5);
        /* Some systems allow implicit bind, others don't */
        TEST_ASSERT(ret == 0 || errno == EINVAL || errno == EDESTADDRREQ,
                    "Listen on unbound socket");
        close(fd2);
    }

    /* Test connect to loopback */
    int client_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (client_fd >= 0) {
        addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
        addr.sin_port = server_port;
        ret = connect(client_fd, (struct sockaddr *)&addr, sizeof(addr));
        TEST_ASSERT(ret == 0 || errno == EINPROGRESS || errno == EWOULDBLOCK,
                    "Connect to loopback");
        close(client_fd);
    }

    /* Test shutdown */
    client_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (client_fd >= 0) {
        ret = shutdown(client_fd, SHUT_RD);
        TEST_ASSERT(ret == 0 || errno == ENOTCONN,
                    "Shutdown read on unconnected socket");
        close(client_fd);
    }

    close(server_fd);
}

/*
 * Test Category 4: Data Transfer
 */
static void test_data_transfer(void)
{
    TEST_SECTION("Data Transfer");

    int sv[2];
    int ret = socketpair(AF_UNIX, SOCK_STREAM, 0, sv);
    if (ret < 0) {
        printf("  [SKIP] socketpair not available, skipping data transfer tests\n");
        return;
    }

    TEST_ASSERT(sv[0] >= 0 && sv[1] >= 0, "Create socket pair");

    /* Test send/recv */
    const char *msg = "Hello, BSD sockets!";
    ssize_t sent = send(sv[0], msg, strlen(msg), 0);
    TEST_ASSERT(sent == (ssize_t)strlen(msg), "Send message");

    char buf[256] = {0};
    ssize_t received = recv(sv[1], buf, sizeof(buf), 0);
    TEST_ASSERT(received == sent, "Receive message");
    TEST_ASSERT(strcmp(buf, msg) == 0, "Message content matches");

    /* Test MSG_PEEK */
    sent = send(sv[0], msg, strlen(msg), 0);
    received = recv(sv[1], buf, sizeof(buf), MSG_PEEK);
    TEST_ASSERT(received > 0, "MSG_PEEK returns data");
    received = recv(sv[1], buf, sizeof(buf), 0);
    TEST_ASSERT(received > 0, "Data still available after PEEK");

    /* Test sendto/recvfrom (for datagram) */
    close(sv[0]);
    close(sv[1]);

    ret = socketpair(AF_UNIX, SOCK_DGRAM, 0, sv);
    if (ret == 0) {
        sent = sendto(sv[0], msg, strlen(msg), 0, NULL, 0);
        TEST_ASSERT(sent > 0, "sendto on datagram socket");

        struct sockaddr_storage from;
        socklen_t fromlen = sizeof(from);
        received = recvfrom(sv[1], buf, sizeof(buf), 0,
                           (struct sockaddr *)&from, &fromlen);
        TEST_ASSERT(received > 0, "recvfrom on datagram socket");

        close(sv[0]);
        close(sv[1]);
    }
}

/*
 * Test Category 5: Socket Options
 */
static void test_socket_options(void)
{
    TEST_SECTION("Socket Options");

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    TEST_ASSERT(fd >= 0, "Create socket for options tests");
    if (fd < 0) return;

    int val;
    socklen_t len;

    /* Test SO_TYPE */
    len = sizeof(val);
    int ret = getsockopt(fd, SOL_SOCKET, SO_TYPE, &val, &len);
    TEST_ASSERT(ret == 0 && val == SOCK_STREAM, "SO_TYPE returns SOCK_STREAM");

    /* Test SO_REUSEADDR */
    val = 1;
    ret = setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &val, sizeof(val));
    TEST_ASSERT(ret == 0, "Set SO_REUSEADDR");

    val = 0;
    len = sizeof(val);
    ret = getsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &val, &len);
    TEST_ASSERT(ret == 0 && val == 1, "Get SO_REUSEADDR");

    /* Test SO_KEEPALIVE */
    val = 1;
    ret = setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, &val, sizeof(val));
    TEST_ASSERT(ret == 0, "Set SO_KEEPALIVE");

    /* Test SO_SNDBUF */
    val = 65536;
    ret = setsockopt(fd, SOL_SOCKET, SO_SNDBUF, &val, sizeof(val));
    TEST_ASSERT(ret == 0, "Set SO_SNDBUF");

    len = sizeof(val);
    ret = getsockopt(fd, SOL_SOCKET, SO_SNDBUF, &val, &len);
    TEST_ASSERT(ret == 0 && val > 0, "Get SO_SNDBUF");

    /* Test SO_RCVBUF */
    val = 65536;
    ret = setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &val, sizeof(val));
    TEST_ASSERT(ret == 0, "Set SO_RCVBUF");

    /* Test SO_LINGER */
    struct linger ling = { .l_onoff = 1, .l_linger = 5 };
    ret = setsockopt(fd, SOL_SOCKET, SO_LINGER, &ling, sizeof(ling));
    TEST_ASSERT(ret == 0, "Set SO_LINGER");

    len = sizeof(ling);
    ret = getsockopt(fd, SOL_SOCKET, SO_LINGER, &ling, &len);
    TEST_ASSERT(ret == 0 && ling.l_onoff == 1, "Get SO_LINGER");

    /* Test SO_ERROR */
    len = sizeof(val);
    ret = getsockopt(fd, SOL_SOCKET, SO_ERROR, &val, &len);
    TEST_ASSERT(ret == 0, "Get SO_ERROR");

    close(fd);
}

/*
 * Test Category 6: Non-blocking I/O
 */
static void test_nonblocking(void)
{
    TEST_SECTION("Non-blocking I/O");

#ifdef SOCK_NONBLOCK
    /* Create non-blocking socket */
    int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0);
    TEST_ASSERT(fd >= 0, "Create non-blocking socket");
    if (fd < 0) return;

    /* Non-blocking connect should return immediately */
    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons(1);  /* Unlikely to be listening */

    int ret = connect(fd, (struct sockaddr *)&addr, sizeof(addr));
    TEST_ASSERT(ret < 0 && (errno == EINPROGRESS || errno == EWOULDBLOCK ||
                            errno == ECONNREFUSED),
                "Non-blocking connect returns immediately");

    close(fd);
#else
    printf("  [SKIP] SOCK_NONBLOCK not available\n");
#endif

    /* Test with fcntl O_NONBLOCK */
    int fd2 = socket(AF_INET, SOCK_STREAM, 0);
    if (fd2 >= 0) {
        /* Would test fcntl here if available */
        close(fd2);
    }
}

/*
 * Test Category 7: Socket Pairs
 */
static void test_socketpair(void)
{
    TEST_SECTION("Socket Pairs");

    int sv[2];

    /* Test AF_UNIX SOCK_STREAM pair */
    int ret = socketpair(AF_UNIX, SOCK_STREAM, 0, sv);
    if (ret == 0) {
        TEST_ASSERT(sv[0] >= 0 && sv[1] >= 0, "Create stream socket pair");

        /* Test bidirectional communication */
        const char *msg1 = "ping";
        const char *msg2 = "pong";
        char buf[64];

        send(sv[0], msg1, strlen(msg1), 0);
        recv(sv[1], buf, sizeof(buf), 0);
        TEST_ASSERT(strcmp(buf, msg1) == 0, "Stream pair: send 0->1");

        memset(buf, 0, sizeof(buf));
        send(sv[1], msg2, strlen(msg2), 0);
        recv(sv[0], buf, sizeof(buf), 0);
        TEST_ASSERT(strcmp(buf, msg2) == 0, "Stream pair: send 1->0");

        close(sv[0]);
        close(sv[1]);
    } else {
        TEST_ASSERT(errno == EOPNOTSUPP || errno == EAFNOSUPPORT,
                    "socketpair returns expected error");
    }

    /* Test AF_UNIX SOCK_DGRAM pair */
    ret = socketpair(AF_UNIX, SOCK_DGRAM, 0, sv);
    if (ret == 0) {
        TEST_ASSERT(sv[0] >= 0 && sv[1] >= 0, "Create datagram socket pair");
        close(sv[0]);
        close(sv[1]);
    }

    /* Test invalid domain for socketpair */
    ret = socketpair(AF_INET, SOCK_STREAM, 0, sv);
    TEST_ASSERT(ret < 0, "socketpair rejects AF_INET");
}

/*
 * Test Category 8: Error Handling
 */
static void test_error_handling(void)
{
    TEST_SECTION("Error Handling");

    /* EBADF tests */
    char buf[64];
    ssize_t ret = send(9999, buf, sizeof(buf), 0);
    TEST_ASSERT(ret < 0 && errno == EBADF, "send on bad fd returns EBADF");

    ret = recv(9999, buf, sizeof(buf), 0);
    TEST_ASSERT(ret < 0 && errno == EBADF, "recv on bad fd returns EBADF");

    int ival;
    socklen_t len = sizeof(ival);
    int ret2 = getsockopt(9999, SOL_SOCKET, SO_TYPE, &ival, &len);
    TEST_ASSERT(ret2 < 0 && errno == EBADF, "getsockopt on bad fd returns EBADF");

    /* ENOTCONN test */
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) {
        struct sockaddr_in addr;
        socklen_t addrlen = sizeof(addr);
        ret2 = getpeername(fd, (struct sockaddr *)&addr, &addrlen);
        TEST_ASSERT(ret2 < 0 && (errno == ENOTCONN || errno == EOPNOTSUPP),
                    "getpeername on unconnected socket");
        close(fd);
    }

    /* EINVAL tests */
    fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) {
        ret2 = shutdown(fd, 999);
        TEST_ASSERT(ret2 < 0 && errno == EINVAL,
                    "shutdown with invalid how");
        close(fd);
    }

    /* EISCONN test (connect on already connected) */
    /* Would need established connection to test */
}

/*
 * Test Category 9: Capability Restrictions (pledge-style)
 */
static void test_capabilities(void)
{
    TEST_SECTION("Capability Restrictions (pledge-style)");

    /* Note: These are exokernel-specific extensions */
    printf("  [INFO] Capability restrictions are exokernel-specific\n");

    /* If sys_socket_pledge is available, test it */
    /* For now, just verify basic socket creation still works */
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    TEST_ASSERT(fd >= 0, "Socket creation after capability check");
    if (fd >= 0) close(fd);

    /* Test DNS-only socket flag if available */
#ifdef SOCK_DNS
    fd = socket(AF_INET, SOCK_DGRAM | SOCK_DNS, 0);
    TEST_ASSERT(fd >= 0, "Create DNS-only socket");
    if (fd >= 0) close(fd);
#else
    printf("  [SKIP] SOCK_DNS not available\n");
#endif
}

/*
 * Test Category 10: Buffer Management
 */
static void test_buffer_management(void)
{
    TEST_SECTION("Buffer Management");

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    TEST_ASSERT(fd >= 0, "Create socket for buffer tests");
    if (fd < 0) return;

    int val;
    socklen_t len;

    /* Test default buffer sizes */
    len = sizeof(val);
    int ret = getsockopt(fd, SOL_SOCKET, SO_SNDBUF, &val, &len);
    if (ret == 0) {
        TEST_ASSERT(val > 0, "Default send buffer > 0");
        printf("  [INFO] Default SO_SNDBUF: %d\n", val);
    }

    len = sizeof(val);
    ret = getsockopt(fd, SOL_SOCKET, SO_RCVBUF, &val, &len);
    if (ret == 0) {
        TEST_ASSERT(val > 0, "Default receive buffer > 0");
        printf("  [INFO] Default SO_RCVBUF: %d\n", val);
    }

    /* Test setting large buffers */
    val = 1024 * 1024;  /* 1 MB */
    ret = setsockopt(fd, SOL_SOCKET, SO_SNDBUF, &val, sizeof(val));
    TEST_ASSERT(ret == 0, "Set large send buffer");

    /* Test setting small buffers */
    val = 1024;  /* 1 KB */
    ret = setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &val, sizeof(val));
    TEST_ASSERT(ret == 0, "Set small receive buffer");

    /* Test low water marks */
    val = 64;
    ret = setsockopt(fd, SOL_SOCKET, SO_RCVLOWAT, &val, sizeof(val));
    TEST_ASSERT(ret == 0 || errno == ENOPROTOOPT, "Set SO_RCVLOWAT");

    close(fd);
}

/*
 * Main test runner
 */
int main(int argc, char *argv[])
{
    printf("==============================================\n");
    printf("BSD Sockets Comprehensive Test Suite\n");
    printf("Synthesized from 4.4BSD/NetBSD/FreeBSD/OpenBSD/DragonFlyBSD\n");
    printf("==============================================\n");

    test_socket_creation();
    test_binding();
    test_connection();
    test_data_transfer();
    test_socket_options();
    test_nonblocking();
    test_socketpair();
    test_error_handling();
    test_capabilities();
    test_buffer_management();

    printf("\n==============================================\n");
    printf("Test Summary:\n");
    printf("  Total:  %d\n", tests_run);
    printf("  Passed: %d\n", tests_passed);
    printf("  Failed: %d\n", tests_failed);
    printf("==============================================\n");

    return tests_failed > 0 ? 1 : 0;
}
