#pragma once

/**
 * @file sys/xattr.h
 * @brief Extended Attributes (xattr) Support for POSIX-2024
 * 
 * Pure C17 implementation of extended file attributes for the FeuerBird
 * ExoKernel LibOS. Provides POSIX-compliant extended attribute operations
 * with exokernel capability integration.
 */

#include <stddef.h>
#include <sys/types.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Extended attribute flags */
#define XATTR_CREATE    0x1     /* Create new attribute, fail if exists */
#define XATTR_REPLACE   0x2     /* Replace existing attribute, fail if not exists */

/* Maximum extended attribute sizes */
#define XATTR_NAME_MAX      255     /* Maximum length of attribute name */
#define XATTR_SIZE_MAX      65536   /* Maximum size of attribute value */
#define XATTR_LIST_MAX      65536   /* Maximum size of attribute list */

/* Extended attribute function declarations */

/**
 * @brief Set an extended attribute value for a file
 * @param path File path
 * @param name Attribute name
 * @param value Attribute value
 * @param size Size of the value  
 * @param flags Control flags (XATTR_CREATE or XATTR_REPLACE)
 * @return 0 on success, -1 on error (errno set)
 */
int setxattr(const char *path, const char *name, const void *value, 
             size_t size, int flags);

/**
 * @brief Get an extended attribute value for a file
 * @param path File path
 * @param name Attribute name
 * @param value Buffer to store attribute value
 * @param size Size of the buffer
 * @return Number of bytes in value, or -1 on error (errno set)
 */
ssize_t getxattr(const char *path, const char *name, void *value, size_t size);

/**
 * @brief List all extended attribute names for a file
 * @param path File path
 * @param list Buffer to store attribute names (null-separated)
 * @param size Size of the buffer
 * @return Number of bytes in list, or -1 on error (errno set)
 */
ssize_t listxattr(const char *path, char *list, size_t size);

/**
 * @brief Remove an extended attribute from a file
 * @param path File path
 * @param name Attribute name to remove
 * @return 0 on success, -1 on error (errno set)
 */
int removexattr(const char *path, const char *name);

/**
 * @brief Set an extended attribute value for a file (by file descriptor)
 * @param fd File descriptor
 * @param name Attribute name
 * @param value Attribute value
 * @param size Size of the value
 * @param flags Control flags (XATTR_CREATE or XATTR_REPLACE)
 * @return 0 on success, -1 on error (errno set)
 */
int fsetxattr(int fd, const char *name, const void *value, 
              size_t size, int flags);

/**
 * @brief Get an extended attribute value for a file (by file descriptor)
 * @param fd File descriptor
 * @param name Attribute name
 * @param value Buffer to store attribute value
 * @param size Size of the buffer
 * @return Number of bytes in value, or -1 on error (errno set)
 */
ssize_t fgetxattr(int fd, const char *name, void *value, size_t size);

/**
 * @brief List all extended attribute names for a file (by file descriptor)
 * @param fd File descriptor
 * @param list Buffer to store attribute names (null-separated)
 * @param size Size of the buffer
 * @return Number of bytes in list, or -1 on error (errno set)
 */
ssize_t flistxattr(int fd, char *list, size_t size);

/**
 * @brief Remove an extended attribute from a file (by file descriptor)
 * @param fd File descriptor
 * @param name Attribute name to remove
 * @return 0 on success, -1 on error (errno set)
 */
int fremovexattr(int fd, const char *name);

/**
 * @brief Set an extended attribute value for a symbolic link (no follow)
 * @param path Symbolic link path
 * @param name Attribute name
 * @param value Attribute value
 * @param size Size of the value
 * @param flags Control flags (XATTR_CREATE or XATTR_REPLACE)
 * @return 0 on success, -1 on error (errno set)
 */
int lsetxattr(const char *path, const char *name, const void *value,
              size_t size, int flags);

/**
 * @brief Get an extended attribute value for a symbolic link (no follow)
 * @param path Symbolic link path
 * @param name Attribute name
 * @param value Buffer to store attribute value
 * @param size Size of the buffer
 * @return Number of bytes in value, or -1 on error (errno set)
 */
ssize_t lgetxattr(const char *path, const char *name, void *value, size_t size);

/**
 * @brief List all extended attribute names for a symbolic link (no follow)
 * @param path Symbolic link path
 * @param list Buffer to store attribute names (null-separated)
 * @param size Size of the buffer
 * @return Number of bytes in list, or -1 on error (errno set)
 */
ssize_t llistxattr(const char *path, char *list, size_t size);

/**
 * @brief Remove an extended attribute from a symbolic link (no follow)
 * @param path Symbolic link path
 * @param name Attribute name to remove
 * @return 0 on success, -1 on error (errno set)
 */
int lremovexattr(const char *path, const char *name);

#ifdef __cplusplus
}
#endif