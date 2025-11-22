#include <stdio.h>
#include <assert.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>

/* Mock declarations for linking */
extern int libos_socket(int domain, int type, int protocol);
extern int libos_bind(int fd, const struct sockaddr *addr, socklen_t len);
extern int libos_listen(int fd, int backlog);
extern int libos_accept(int fd, struct sockaddr *addr, socklen_t *len);
extern int libos_connect(int fd, const struct sockaddr *addr, socklen_t len);
extern long libos_send(int fd, const void *buf, size_t len, int flags);
extern long libos_recv(int fd, void *buf, size_t len, int flags);
extern int libos_close(int fd);

int main() {
    printf("Testing BSD Sockets...\n");

    int sockfd = libos_socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) {
        printf("Socket creation failed: %d\n", sockfd);
        return 1;
    }
    printf("Socket created, fd=%d\n", sockfd);

    struct sockaddr_in addr;
    addr.sin_family = AF_INET;
    addr.sin_port = htons(8080);
    addr.sin_addr.s_addr = INADDR_ANY;

    int ret = libos_bind(sockfd, (struct sockaddr *)&addr, sizeof(addr));
    if (ret < 0) {
        printf("Bind failed: %d\n", ret);
        return 1;
    }
    printf("Bind successful\n");

    ret = libos_listen(sockfd, 5);
    if (ret < 0) {
        printf("Listen failed: %d\n", ret);
        return 1;
    }
    printf("Listen successful\n");

    struct sockaddr_in client_addr;
    socklen_t len = sizeof(client_addr);
    int clientfd = libos_accept(sockfd, (struct sockaddr *)&client_addr, &len);
    if (clientfd < 0) {
        printf("Accept failed (expected for non-blocking mock? or implementation returns mock client immediately?)\n");
        // Our mock accept returns a new socket immediately
        return 1;
    }
    printf("Accept successful, client fd=%d\n", clientfd);

    // Test Send/Recv
    char *msg = "Hello";
    long sent = libos_send(clientfd, msg, 5, 0);
    if (sent != 5) {
         printf("Send failed: %ld\n", sent);
         return 1;
    }
    printf("Send successful\n");

    // Close
    // libos_close(clientfd); // Helper not linked in this unit test unless we include posix.c
    // libos_close(sockfd);

    printf("BSD Socket tests passed.\n");
    return 0;
}
