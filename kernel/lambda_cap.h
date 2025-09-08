/**
 * @file lambda_cap.h  
 * @brief Pi-Calculus Lambda Capability Engine with Superforce Integration
 * 
 * Complete header definitions for the unified mathematical architecture
 * integrating Pi-calculus, Superforce theory, and exokernel capabilities.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include "types.h"
#include "cap.h"
#include "spinlock.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Forward declarations */
struct proc;
struct exo_cap;

/* Pi-Calculus Channel for lambda communication */
struct pi_channel {
    cap_id_t send_cap;        /* Send capability */
    cap_id_t recv_cap;        /* Receive capability */
    volatile uint32_t seq;    /* Sequence number */
    bool used_send;           /* Affine type: used send */
    bool used_recv;           /* Affine type: used recv */
    struct spinlock lock;     /* Channel synchronization */
    
    /* Network transport layer */
    uint32_t local_addr;      /* Local network address */
    uint32_t remote_addr;     /* Remote network address */
    uint16_t local_port;      /* Local port */
    uint16_t remote_port;     /* Remote port */
    
    /* Message buffer */
    void *msg_buffer;         /* Message data buffer */
    uint32_t buffer_size;     /* Buffer size in bytes */
    uint32_t msg_len;         /* Current message length */
};

/* S-Expression node for LISP-like evaluation */
typedef enum s_expr_type {
    S_ATOM,                   /* Atomic symbol */
    S_CONS,                   /* Cons cell (car, cdr) */
    S_LAMBDA,                 /* Lambda abstraction */
    S_APPLY,                  /* Function application */
    S_INTEGER,                /* Integer literal */
    S_STRING                  /* String literal */
} s_expr_type_t;

struct s_expr {
    s_expr_type_t type;
    union {
        struct { 
            char *symbol; 
            uint32_t symbol_len; 
        } atom;
        struct { 
            struct s_expr *car;
            struct s_expr *cdr; 
        } cons;
        struct { 
            char *param; 
            uint32_t param_len;
            struct s_expr *body; 
        } lambda;
        struct { 
            struct s_expr *func;
            struct s_expr *arg; 
        } apply;
        struct {
            int64_t value;
        } integer;
        struct {
            char *data;
            uint32_t length;
        } string;
    } data;
    struct s_expr *next;      /* For memory management */
};

/* Octonion structure for 8-dimensional mathematics */
typedef struct octonion {
    union {
        double coeffs[8];           /* e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇ */
        struct {
            double e0, e1, e2, e3;  /* Quaternion-like part */
            double e4, e5, e6, e7;  /* Octonion extension */
        };
        struct {
            double real;            /* Real part */
            double i, j, k;         /* Quaternion imaginary */
            double l, m, n, o;      /* Octonion extension */
        };
    };
} octonion_t;

/* Superforce-powered Lambda capability integrating all theories */
struct lambda_cap {
    /* Exokernel foundation */
    cap_id_t cap_id;              /* Capability table ID */
    struct exo_cap exec_cap;      /* Execution capability */
    
    /* Pi-Calculus process structure */
    struct pi_channel **channels;    /* Array of communication channels */
    uint32_t channel_count;       /* Number of channels */
    uint32_t max_channels;        /* Maximum channels allocated */
    
    /* Lambda calculus evaluation engine */
    struct s_expr *expression;    /* S-expression tree */
    void (*native_fn)(void *);    /* Native function pointer */
    void *env;                    /* Environment/closure */
    
    /* Superforce energy management */
    uint64_t energy_quanta;       /* Energy in Planck units */
    uint32_t fuel;                /* Execution fuel/gas */
    uint32_t max_fuel;            /* Maximum fuel allocation */
    
    /* Octonion mathematics for 8D state */
    octonion_t state_vector;      /* 8-dimensional system state */
    octonion_t transformation;    /* State transformation matrix */
    
    /* Category-theoretic composition */
    uint32_t bigraph_id;          /* Bigraph node identifier */
    bool consumed;                /* Affine: used once */
    
    /* Concurrency control */
    volatile uint32_t ref_count;  /* Reference counting */
    struct spinlock lock;         /* Synchronization */
};

/* Function pointer types */
typedef int (*lambda_fn_t)(void *env);
typedef int (*s_expr_evaluator_t)(struct s_expr *expr, void *env, struct s_expr **result);

/* =========================== Core Functions =========================== */

/* Lambda capability management */
struct lambda_cap *lambda_cap_create(void (*fn)(void *), void *env, struct exo_cap cap);
void lambda_cap_destroy(struct lambda_cap *lc);
int lambda_cap_use(struct lambda_cap *lc, int fuel);
int lambda_cap_delegate(struct lambda_cap *lc, uint16_t new_owner);
int lambda_cap_revoke(struct lambda_cap *lc);

/* Pi-calculus channel operations */
int lambda_cap_create_channel(struct lambda_cap *sender, struct lambda_cap *receiver, 
                             struct pi_channel **channel_out);
int lambda_cap_channel_send(struct pi_channel *ch, struct s_expr *expr);
int lambda_cap_channel_recv(struct pi_channel *ch, struct s_expr **expr_out);
void pi_channel_destroy(struct pi_channel *ch);

/* Network transport for Pi-calculus channels */
int pi_channel_connect(struct pi_channel *ch, uint32_t addr, uint16_t port);
int pi_channel_listen(struct pi_channel *ch, uint16_t port);
int pi_channel_accept(struct pi_channel *listener, struct pi_channel **client_out);
int pi_channel_send_raw(struct pi_channel *ch, const void *data, uint32_t len);
int pi_channel_recv_raw(struct pi_channel *ch, void *buffer, uint32_t max_len);

/* S-expression operations */
struct s_expr *s_expr_alloc(s_expr_type_t type);
void s_expr_destroy(struct s_expr *expr);
struct s_expr *s_expr_atom(const char *symbol);
struct s_expr *s_expr_cons(struct s_expr *car, struct s_expr *cdr);
struct s_expr *s_expr_lambda(const char *param, struct s_expr *body);
struct s_expr *s_expr_apply(struct s_expr *func, struct s_expr *arg);
struct s_expr *s_expr_integer(int64_t value);
struct s_expr *s_expr_string(const char *str, uint32_t len);

/* S-expression evaluation engine */
int s_expr_eval(struct s_expr *expr, void *env, struct s_expr **result);
int s_expr_print(struct s_expr *expr, char *buffer, uint32_t max_len);
struct s_expr *s_expr_parse(const char *input, uint32_t len);

/* Octonion mathematics */
octonion_t octonion_zero(void);
octonion_t octonion_one(void);
octonion_t octonion_create(double e0, double e1, double e2, double e3,
                          double e4, double e5, double e6, double e7);
octonion_t octonion_add(octonion_t a, octonion_t b);
octonion_t octonion_sub(octonion_t a, octonion_t b);
octonion_t octonion_mul(octonion_t a, octonion_t b);
octonion_t octonion_conjugate(octonion_t a);
double octonion_norm_squared(octonion_t a);
double octonion_norm(octonion_t a);
octonion_t octonion_normalize(octonion_t a);

/* Superforce energy management */
uint64_t superforce_energy_quantum(void);
int lambda_cap_charge_energy(struct lambda_cap *lc, uint64_t energy_cost);
int lambda_cap_transfer_energy(struct lambda_cap *src, struct lambda_cap *dst, uint64_t amount);
uint64_t lambda_cap_available_energy(struct lambda_cap *lc);

/* Category theory and bigraph operations */
int lambda_cap_compose_parallel(struct lambda_cap *left, struct lambda_cap *right,
                               struct lambda_cap **result);
int lambda_cap_compose_sequential(struct lambda_cap *first, struct lambda_cap *second,
                                 struct lambda_cap **result);
int lambda_cap_create_bigraph_node(struct lambda_cap *lc, uint32_t node_type);
int lambda_cap_connect_bigraph_edge(struct lambda_cap *src, struct lambda_cap *dst);

/* Memory management */
void lambda_cap_memory_init(void);
void lambda_cap_memory_cleanup(void);
void *lambda_cap_alloc(uint32_t size);
void lambda_cap_free(void *ptr);

/* Error codes */
#define LAMBDA_CAP_SUCCESS           0
#define LAMBDA_CAP_ERROR_NOMEM      -1
#define LAMBDA_CAP_ERROR_INVALID    -2
#define LAMBDA_CAP_ERROR_CONSUMED   -3
#define LAMBDA_CAP_ERROR_NO_ENERGY  -4
#define LAMBDA_CAP_ERROR_NO_FUEL    -5
#define LAMBDA_CAP_ERROR_NETWORK    -6
#define LAMBDA_CAP_ERROR_PARSE      -7
#define LAMBDA_CAP_ERROR_EVAL       -8

/* Constants */
#define LAMBDA_CAP_MAX_CHANNELS     256
#define LAMBDA_CAP_DEFAULT_FUEL     1000
#define LAMBDA_CAP_MAX_FUEL         1000000
#define LAMBDA_CAP_MSG_BUFFER_SIZE  8192
#define LAMBDA_CAP_MAX_SYMBOL_LEN   256
#define LAMBDA_CAP_MAX_STRING_LEN   4096

/* Superforce constant: c^4/G ≈ 10^44 N */
#define SUPERFORCE_CONSTANT_MANTISSA 1211027742
#define SUPERFORCE_CONSTANT_EXPONENT 35

/* Planck scale energy quantum */
#define PLANCK_ENERGY_QUANTUM_MANTISSA 1956177
#define PLANCK_ENERGY_QUANTUM_EXPONENT -9

#ifdef __cplusplus
}
#endif