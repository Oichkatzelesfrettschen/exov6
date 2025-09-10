#ifndef AETHER_NN_H
#define AETHER_NN_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef float ann_f32;
typedef uint32_t ann_u32;
typedef size_t ann_usize;

/* ========================= Arena ========================= */
typedef struct {
  unsigned char *base;
  ann_usize size;
  ann_usize used;
} ann_Arena;

void ann_arena_init(ann_Arena *A, void *buffer, ann_usize size);
void *ann_arena_alloc(ann_Arena *A, ann_usize bytes, ann_usize align);
void ann_arena_reset(ann_Arena *A);

/* ========================= RNG ========================= */
typedef struct {
  ann_u32 s;
} ann_XRand;

ann_u32 ann_xrand_u32(ann_XRand *r);
ann_f32 ann_xrand_uniform(ann_XRand *r);
ann_f32 ann_xrand_normalish(ann_XRand *r);

/* ========================= Tensor ========================= */
typedef struct {
  ann_f32 *data;
  ann_usize n;
} ann_Tensor;

ann_Tensor ann_tensor_new(ann_Arena *A, ann_usize n);
void ann_tensor_zero(ann_Tensor t);
void ann_tensor_copy(ann_Tensor dst, ann_Tensor src);

ann_f32 ann_dot(const ann_f32 *a, const ann_f32 *b, ann_usize n);

/* ========================= Activations / losses ========================= */
ann_f32 ann_sigmoid(ann_f32 z);
ann_f32 ann_binary_ce(ann_f32 yhat, ann_f32 y);
ann_f32 ann_softmax_inplace(ann_f32 *z, ann_usize C);
ann_f32 ann_softmax_ce_from_logits(ann_f32 *z, ann_usize C, ann_usize y_true);

/* ========================= Embedding + Aggregators =========================
 */
typedef struct {
  ann_usize vocab;
  ann_usize dim;
  ann_f32 *table;
} ann_Embedding;

typedef enum {
  ANN_AGG_SUM = 0,
  ANN_AGG_SHIFT = 1,
  ANN_AGG_CCONV = 2
} ann_AggKind;

typedef struct {
  ann_AggKind kind;
  ann_usize dim;
  ann_usize max_pos;
  ann_f32 *R; /* [max_pos][dim] used in CCONV */
  int norm;   /* 0: none, 1: divide by sqrt(k) */
} ann_Aggregator;

ann_Embedding ann_embedding_new(ann_Arena *A, ann_usize vocab, ann_usize dim,
                                ann_XRand *rng);
ann_Aggregator ann_aggregator_new(ann_Arena *A, ann_AggKind k, ann_usize dim,
                                  ann_usize max_pos, int norm, ann_XRand *rng);
ann_Tensor ann_embedding_forward_agg(ann_Arena *A, const ann_Embedding *E,
                                     const ann_usize *idx, ann_usize k,
                                     const ann_Aggregator *G);
void ann_embedding_sgd_agg(ann_Embedding *E, const ann_usize *idx, ann_usize k,
                           ann_Tensor g, ann_f32 lr, const ann_Aggregator *G,
                           ann_Arena *scratch);

/* ========================= Dense + Optimizers ========================= */
typedef struct {
  ann_usize in;
  ann_usize out;
  ann_f32 *W;
  ann_f32 *b;
  ann_f32 *momW;
  ann_f32 *momB;
  ann_f32 *mW;
  ann_f32 *vW;
  ann_f32 *mB;
  ann_f32 *vB;
} ann_Dense;

typedef enum { ANN_OPT_SGD, ANN_OPT_MOMENTUM, ANN_OPT_ADAM } ann_OptimKind;

typedef struct {
  ann_OptimKind kind;
  ann_f32 lr;
  ann_f32 l2;
  ann_f32 mu;
  ann_f32 beta1;
  ann_f32 beta2;
  ann_f32 eps;
  ann_u32 t;
} ann_Optim;

ann_Dense ann_dense_new(ann_Arena *A, ann_usize in, ann_usize out,
                        ann_XRand *rng);
ann_Tensor ann_dense_forward(ann_Arena *A, const ann_Dense *L, ann_Tensor x);
void ann_dense_opt_prepare(ann_Arena *A, ann_Dense *L, const ann_Optim *opt);
ann_f32 ann_dense_train_logistic(ann_Dense *L, ann_Tensor x, ann_f32 y_true,
                                 ann_Optim *opt);
ann_f32 ann_softmax_ce_from_logits_train(ann_Dense *L, ann_Tensor x,
                                         ann_usize y_true, ann_Optim *opt,
                                         ann_f32 *out_logits);

/* ========================= Quantized Dense (int8) ========================= */
typedef struct {
  ann_usize in;
  ann_usize out;
  int8_t *Wq;
  ann_f32 *scale;
  ann_f32 *b;
} ann_QDense;

ann_QDense ann_qdense_from_dense(ann_Arena *A, const ann_Dense *L);
ann_Tensor ann_qdense_forward(ann_Arena *A, const ann_QDense *Q, ann_Tensor x);

#ifdef __cplusplus
}
#endif

#endif /* AETHER_NN_H */
