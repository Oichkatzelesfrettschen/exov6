#include "microkernel/microkernel.h"
#include "user.h"

static int print_step(void *env) {
    (void)env;
    printf(1, "demo lambda executed\n");
    return 1;
}

int main(void) {
    microkernel_register();

    exo_cap page = mk_cap_alloc_page();
    mk_cap_free_page(page);

    lambda_cap_t *lc = mk_lambda_cap_create(print_step, 0, (exo_cap){0});
    mk_lambda_cap_use(lc, 1);
    mk_lambda_cap_destroy(lc);

    const char msg[] = "hello";
    mk_route_message((exo_cap){0}, msg, sizeof(msg));

    return 0;
}
