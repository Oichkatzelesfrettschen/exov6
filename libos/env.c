/**
 * @file env.c
 * @brief Minimal environment variable helpers for libos.
 */

#include <stdlib.h>
#include <string.h>

/**
 * @brief Set an environment variable.
 * @param key   Name of the variable.
 * @param value Value to assign.
 * @return 0 on success, negative on failure.
 */
int libos_setenv(const char *key, const char *value)
{
  if (!key || !value) return -1;
  return setenv(key, value, 1) == 0 ? 0 : -1;
}

/**
 * @brief Get an environment variable.
 * @param key Name of the variable.
 * @return Pointer to value or NULL if not set.
 */
const char *libos_getenv(const char *key)
{
  if (!key) return NULL;
  return getenv(key);
}

