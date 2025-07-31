#include "service.h"

/** Wrapper that forwards to the system call stub. */
int libos_service_register(const char *name, const char *path,
                           service_options_t opts) {
  return service_register(name, path, opts);
}

/** Wrapper that forwards to the system call stub. */
int libos_service_add_dependency(const char *name, const char *dependency) {
  return service_add_dependency(name, dependency);
}
