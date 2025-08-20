#pragma once
#include "kernel_compat.h"

#ifdef __cplusplus
extern "C" {
#endif

/** Service registration options. */
typedef struct service_options {
  bool auto_restart; /**< Restart service on failure. */
} service_options_t;

int service_register(const char *name, const char *path,
                     service_options_t opts);
int service_add_dependency(const char *name, const char *dependency);
#ifdef EXO_KERNEL
struct proc;
void service_notify_exit(struct proc *p);
#endif

#ifdef __cplusplus
}
#endif
