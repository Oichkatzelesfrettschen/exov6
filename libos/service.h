/**
 * @file service.h
 * @brief LibOS service management header
 *
 * Service registration and dependency management for LibOS components.
 */
#pragma once

#include <stdint.h>

/* Service options for registration */
typedef uint32_t service_options_t;

#define SERVICE_OPT_NONE      0x00
#define SERVICE_OPT_REQUIRED  0x01
#define SERVICE_OPT_AUTOSTART 0x02

/* Forward declaration of system call stubs */
int service_register(const char *name, const char *path, service_options_t opts);
int service_add_dependency(const char *name, const char *dependency);
