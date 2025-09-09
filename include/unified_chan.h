#pragma once

/**
 * @file unified_chan.h
 * @brief Unified Channel Trait System for ExoV6
 * 
 * Eliminates architectural redundancy by providing a composable channel
 * system with pluggable properties instead of three parallel implementations.
 * 
 * Replaces:
 * - CHAN_DECLARE (basic fixed-size)
 * - AFFINE_CHAN_DECLARE (linear-typed)  
 * - CHAN_DECLARE_VAR (variable-size)
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include "types.h"
#include "exo.h"

/* Channel property flags - composable traits */
#define CHAN_FIXED         (1 << 0)  /* Fixed-size messages */
#define CHAN_VAR           (1 << 1)  /* Variable-size messages */
#define CHAN_AFFINE        (1 << 2)  /* Linear usage tracking */
#define CHAN_PERSISTENT    (1 << 3)  /* Survives process death */
#define CHAN_BOUNDED       (1 << 4)  /* Bounded message queue */
#define CHAN_SECURED       (1 << 5)  /* Capability-secured */

/* Forward declarations */
struct unified_chan;
typedef struct unified_chan unified_chan_t;

/* Message type descriptor with encoding/decoding */
typedef struct msg_type_desc {
    size_t msg_size;           /* Maximum message size */
    size_t min_size;           /* Minimum message size (for variable) */
    size_t (*encode_fn)(const void *msg, unsigned char *buf);
    size_t (*decode_fn)(void *msg, const unsigned char *buf);
} msg_type_desc_t;

/* Channel property extensions */
typedef union chan_extensions {
    struct {
        int send_count;        /* Sends remaining */
        int recv_count;        /* Receives remaining */
    } affine;
    
    struct {
        size_t max_messages;   /* Maximum queued messages */
        size_t current_count;  /* Current message count */
    } bounded;
    
    struct {
        uint32_t required_caps; /* Required capability mask */
        exo_cap owner_cap;      /* Owner capability */
    } secured;
} chan_extensions_t;

/* Unified channel base structure */
struct unified_chan {
    const msg_type_desc_t *type_desc;  /* Message type information */
    uint32_t properties;               /* Property flags */
    chan_extensions_t ext;             /* Property-specific data */
    void *impl_data;                   /* Implementation-specific data */
};

/* Core channel operations */
unified_chan_t *unified_chan_create(const msg_type_desc_t *desc, uint32_t properties);
void unified_chan_destroy(unified_chan_t *c);

int unified_chan_send(unified_chan_t *c, exo_cap dest, const void *msg, size_t len);
int unified_chan_recv(unified_chan_t *c, exo_cap src, void *msg, size_t max_len);

/* Property configuration */
int unified_chan_configure_affine(unified_chan_t *c, int max_sends, int max_recvs);
int unified_chan_configure_bounded(unified_chan_t *c, size_t max_messages);
int unified_chan_configure_secured(unified_chan_t *c, uint32_t required_caps, exo_cap owner);

/* Unified macro system - replaces all three redundant implementations */
#define UNIFIED_CHAN_DECLARE(name, type, props)                                   \
  static size_t name##_encode_fn(const void *msg, unsigned char *buf) {          \
    if (buf) *(type*)buf = *(const type*)msg;                                    \
    return sizeof(type);                                                         \
  }                                                                              \
  static size_t name##_decode_fn(void *msg, const unsigned char *buf) {         \
    *(type*)msg = *(const type*)buf;                                             \
    return sizeof(type);                                                         \
  }                                                                              \
  static const msg_type_desc_t name##_typedesc = {                              \
      .msg_size = sizeof(type),                                                  \
      .min_size = sizeof(type),                                                  \
      .encode_fn = name##_encode_fn,                                             \
      .decode_fn = name##_decode_fn                                              \
  };                                                                             \
  typedef struct {                                                               \
    unified_chan_t base;                                                         \
  } name##_t;                                                                    \
  static inline name##_t *name##_create(void) {                                  \
    return (name##_t *)unified_chan_create(&name##_typedesc, props);             \
  }                                                                              \
  static inline void name##_destroy(name##_t *c) {                              \
    unified_chan_destroy(&c->base);                                             \
  }                                                                              \
  static inline int name##_send(name##_t *c, exo_cap dest, const type *m) {     \
    return unified_chan_send(&c->base, dest, m, sizeof(type));                  \
  }                                                                              \
  static inline int name##_recv(name##_t *c, exo_cap src, type *m) {            \
    return unified_chan_recv(&c->base, src, m, sizeof(type));                   \
  }

/* Convenience macros for common channel types */
#define CHAN_DECLARE(name, type) \
    UNIFIED_CHAN_DECLARE(name, type, CHAN_FIXED)

#define AFFINE_CHAN_DECLARE(name, type) \
    UNIFIED_CHAN_DECLARE(name, type, CHAN_FIXED | CHAN_AFFINE)

#define CHAN_DECLARE_VAR(name, type) \
    UNIFIED_CHAN_DECLARE(name, type, CHAN_VAR)

/* Compile-time assertions */
_Static_assert(sizeof(unified_chan_t) <= 64, "Unified channel too large");
_Static_assert(_Alignof(unified_chan_t) >= 8, "Channel alignment insufficient");

#endif /* UNIFIED_CHAN_H */