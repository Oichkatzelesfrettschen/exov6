#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>
#include <fcntl.h>

#define NUM_THREADS 4
#define MSGS_PER_THREAD 1000

int pipe_fds[2];

void *sender(void *arg) {
    int id = *(int*)arg;
    for (int i = 0; i < MSGS_PER_THREAD; i++) {
        int val = id * 10000 + i;
        if (write(pipe_fds[1], &val, sizeof(int)) != sizeof(int)) {
            perror("write");
        }
        if (i % 100 == 0) usleep(100); // Random delays
    }
    return NULL;
}

void *receiver(void *arg) {
    int total_msgs = NUM_THREADS * MSGS_PER_THREAD;
    for (int i = 0; i < total_msgs; i++) {
        int val;
        if (read(pipe_fds[0], &val, sizeof(int)) != sizeof(int)) {
            perror("read");
        }
    }
    return NULL;
}

int main(void) {
    printf("Starting IPC stress test...\n");
    if (pipe(pipe_fds) == -1) {
        perror("pipe");
        return 1;
    }

    pthread_t threads[NUM_THREADS];
    pthread_t rx_thread;
    int ids[NUM_THREADS];

    pthread_create(&rx_thread, NULL, receiver, NULL);

    for (int i = 0; i < NUM_THREADS; i++) {
        ids[i] = i;
        pthread_create(&threads[i], NULL, sender, &ids[i]);
    }

    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    pthread_join(rx_thread, NULL);

    printf("IPC stress test passed.\n");
    return 0;
}
