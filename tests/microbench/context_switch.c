#include <stdio.h>
#include <stdint.h>
#include <string.h>

typedef struct context64 {
    unsigned long r15;
    unsigned long r14;
    unsigned long r13;
    unsigned long r12;
    unsigned long rbx;
    unsigned long rbp;
    unsigned long rip;
} context_t;

void swtch(context_t **old, context_t *new);

static inline uint64_t rdtsc(void)
{
    unsigned hi, lo;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

#define ITER 100000

static context_t *main_ctx_ptr;
static context_t *thread_ctx;
static context_t main_ctx_storage;

static void thread_func(void)
{
    for (;;)
        swtch(&thread_ctx, main_ctx_ptr);
}

int main(void)
{
    static unsigned char stack[8192];
    main_ctx_ptr = &main_ctx_storage;

    thread_ctx = (context_t *)(stack + sizeof(stack) - sizeof(*thread_ctx));
    memset(thread_ctx, 0, sizeof(*thread_ctx));
    thread_ctx->rip = (unsigned long)thread_func;

    uint64_t start = rdtsc();
    for (int i = 0; i < ITER; i++)
        swtch(&main_ctx_ptr, thread_ctx);
    uint64_t end = rdtsc();

    printf("context switch: %lu cycles\n", (end - start) / (ITER * 2));
    return 0;
}
