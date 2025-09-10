#include "aether_nn.h"

#include <math.h>
#include <stdalign.h>
#include <stdlib.h>
#include <string.h>

/* ========================= Arena ========================= */
void ann_arena_init(ann_Arena *A, void *buffer, ann_usize size) {
  A->base = (unsigned char *)buffer;
  A->size = size;
  A->used = 0;
}

void *ann_arena_alloc(ann_Arena *A, ann_usize bytes, ann_usize align) {
  ann_usize p = (ann_usize)(A->base + A->used);
  ann_usize aligned = (p + (align - 1)) & ~(align - 1);
  ann_usize new_used = (aligned - (ann_usize)A->base) + bytes;
  if (new_used > A->size)
    return NULL;
  A->used = new_used;
  return (void *)aligned;
}

void ann_arena_reset(ann_Arena *A) { A->used = 0; }

/* ========================= RNG ========================= */
ann_u32 ann_xrand_u32(ann_XRand *r) {
  ann_u32 x = r->s;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  r->s = x ? x : 0x9E3779B9u;
  return r->s;
}

ann_f32 ann_xrand_uniform(ann_XRand *r) {
  return (ann_xrand_u32(r) >> 8) * (1.0f / 16777216.0f);
}

ann_f32 ann_xrand_normalish(ann_XRand *r) {
  ann_f32 u1 = fmaxf(1e-7f, ann_xrand_uniform(r));
  ann_f32 u2 = ann_xrand_uniform(r);
  return sqrtf(-2.0f * logf(u1)) * cosf(6.28318530718f * u2);
}

/* ========================= Tensor ========================= */
ann_Tensor ann_tensor_new(ann_Arena *A, ann_usize n) {
  ann_Tensor t = {0};
  t.data = (ann_f32 *)ann_arena_alloc(A, n * sizeof(ann_f32), alignof(ann_f32));
  t.n = n;
  return t;
}

void ann_tensor_zero(ann_Tensor t) {
  for (ann_usize i = 0; i < t.n; i++)
    t.data[i] = 0.0f;
}

void ann_tensor_copy(ann_Tensor dst, ann_Tensor src) {
  for (ann_usize i = 0; i < dst.n; i++)
    dst.data[i] = src.data[i];
}

ann_f32 ann_dot(const ann_f32 *a, const ann_f32 *b, ann_usize n) {
  ann_f32 s = 0.0f;
  for (ann_usize i = 0; i < n; i++)
    s += a[i] * b[i];
  return s;
}

/* ========================= Activations / losses ========================= */
ann_f32 ann_sigmoid(ann_f32 z) { return 1.0f / (1.0f + expf(-z)); }

ann_f32 ann_binary_ce(ann_f32 yhat, ann_f32 y) {
  const ann_f32 e = 1e-7f;
  yhat = fmaxf(e, fminf(1.0f - e, yhat));
  return -(y * logf(yhat) + (1.0f - y) * logf(1.0f - yhat));
}

ann_f32 ann_softmax_inplace(ann_f32 *z, ann_usize C) {
  ann_f32 m = z[0];
  for (ann_usize i = 1; i < C; i++)
    if (z[i] > m)
      m = z[i];
  ann_f32 sum = 0.0f;
  for (ann_usize i = 0; i < C; i++) {
    z[i] = expf(z[i] - m);
    sum += z[i];
  }
  ann_f32 inv = 1.0f / sum;
  for (ann_usize i = 0; i < C; i++)
    z[i] *= inv;
  return logf(sum) + m;
}

ann_f32 ann_softmax_ce_from_logits(ann_f32 *z, ann_usize C, ann_usize y_true) {
  (void)ann_softmax_inplace(z, C);
  const ann_f32 e = 1e-9f;
  return -logf(fmaxf(e, z[y_true]));
}

/* ========================= Embedding + Aggregators =========================
 */
ann_Embedding ann_embedding_new(ann_Arena *A, ann_usize vocab, ann_usize dim,
                                ann_XRand *rng) {
  ann_Embedding E = {.vocab = vocab, .dim = dim, .table = NULL};
  E.table = (ann_f32 *)ann_arena_alloc(A, vocab * dim * sizeof(ann_f32),
                                       alignof(ann_f32));
  ann_f32 scale = sqrtf(6.0f / (ann_f32)dim);
  for (ann_usize i = 0; i < vocab * dim; i++)
    E.table[i] = (ann_xrand_uniform(rng) * 2.0f - 1.0f) * scale;
  return E;
}

static void ann_rotate_right(const ann_f32 *x, ann_f32 *out, ann_usize n,
                             ann_usize shift) {
  shift %= n;
  if (shift == 0) {
    for (ann_usize i = 0; i < n; i++)
      out[i] = x[i];
    return;
  }
  for (ann_usize d = 0; d < n; d++) {
    ann_usize s = (d + n - shift) % n;
    out[d] = x[s];
  }
}

static void ann_rotate_left(const ann_f32 *x, ann_f32 *out, ann_usize n,
                            ann_usize shift) {
  shift %= n;
  if (shift == 0) {
    for (ann_usize i = 0; i < n; i++)
      out[i] = x[i];
    return;
  }
  for (ann_usize d = 0; d < n; d++) {
    ann_usize s = (d + shift) % n;
    out[d] = x[s];
  }
}

static void ann_cconv(const ann_f32 *a, const ann_f32 *b, ann_f32 *out,
                      ann_usize n) {
  for (ann_usize d = 0; d < n; d++) {
    ann_f32 acc = 0.0f;
    for (ann_usize m = 0; m < n; m++) {
      ann_usize q = (d + n - (m % n)) % n;
      acc += a[m] * b[q];
    }
    out[d] = acc;
  }
}

static void ann_cconv_grad_wrt_a(const ann_f32 *g, const ann_f32 *b,
                                 ann_f32 *out, ann_usize n) {
  for (ann_usize m = 0; m < n; m++) {
    ann_f32 acc = 0.0f;
    for (ann_usize d = 0; d < n; d++) {
      ann_usize idx = (d + n - (m % n)) % n;
      acc += g[d] * b[idx];
    }
    out[m] = acc;
  }
}

ann_Aggregator ann_aggregator_new(ann_Arena *A, ann_AggKind k, ann_usize dim,
                                  ann_usize max_pos, int norm, ann_XRand *rng) {
  ann_Aggregator G = {
      .kind = k, .dim = dim, .max_pos = max_pos, .R = NULL, .norm = norm};
  if (k == ANN_AGG_CCONV) {
    G.R = (ann_f32 *)ann_arena_alloc(A, max_pos * dim * sizeof(ann_f32),
                                     alignof(ann_f32));
    for (ann_usize p = 0; p < max_pos; p++) {
      ann_f32 *row = &G.R[p * dim];
      ann_f32 normv = 0.0f;
      for (ann_usize d = 0; d < dim; d++) {
        row[d] = ann_xrand_normalish(rng);
        normv += row[d] * row[d];
      }
      normv = sqrtf(fmaxf(normv, 1e-12f));
      for (ann_usize d = 0; d < dim; d++)
        row[d] /= normv;
    }
  }
  return G;
}

ann_Tensor ann_embedding_forward_agg(ann_Arena *A, const ann_Embedding *E,
                                     const ann_usize *idx, ann_usize k,
                                     const ann_Aggregator *G) {
  ann_Tensor out = ann_tensor_new(A, E->dim);
  ann_tensor_zero(out);
  ann_Tensor tmp = ann_tensor_new(A, E->dim);
  for (ann_usize j = 0; j < k; j++) {
    ann_usize r = idx[j];
    if (r >= E->vocab)
      continue;
    const ann_f32 *row = &E->table[r * E->dim];
    if (G->kind == ANN_AGG_SUM) {
      for (ann_usize d = 0; d < E->dim; d++)
        out.data[d] += row[d];
    } else if (G->kind == ANN_AGG_SHIFT) {
      ann_rotate_right(row, tmp.data, E->dim, j % E->dim);
      for (ann_usize d = 0; d < E->dim; d++)
        out.data[d] += tmp.data[d];
    } else {
      const ann_f32 *Rj = &G->R[(j % G->max_pos) * E->dim];
      ann_cconv(row, Rj, tmp.data, E->dim);
      for (ann_usize d = 0; d < E->dim; d++)
        out.data[d] += tmp.data[d];
    }
  }
  if (G->norm && k > 0) {
    ann_f32 s = 1.0f / sqrtf((ann_f32)k);
    for (ann_usize d = 0; d < E->dim; d++)
      out.data[d] *= s;
  }
  return out;
}

void ann_embedding_sgd_agg(ann_Embedding *E, const ann_usize *idx, ann_usize k,
                           ann_Tensor g, ann_f32 lr, const ann_Aggregator *G,
                           ann_Arena *scratch) {
  if (G->kind == ANN_AGG_SUM) {
    for (ann_usize j = 0; j < k; j++) {
      ann_usize r = idx[j];
      if (r >= E->vocab)
        continue;
      ann_f32 *row = &E->table[r * E->dim];
      ann_f32 scale = (G->norm && k > 0) ? (1.0f / sqrtf((ann_f32)k)) : 1.0f;
      for (ann_usize d = 0; d < E->dim; d++)
        row[d] -= lr * scale * g.data[d];
    }
    return;
  }
  ann_Tensor tmp = ann_tensor_new(scratch, E->dim);
  for (ann_usize j = 0; j < k; j++) {
    ann_usize r = idx[j];
    if (r >= E->vocab)
      continue;
    ann_f32 *row = &E->table[r * E->dim];
    if (G->kind == ANN_AGG_SHIFT) {
      ann_rotate_left(g.data, tmp.data, E->dim, j % E->dim);
    } else {
      const ann_f32 *Rj = &G->R[(j % G->max_pos) * E->dim];
      ann_cconv_grad_wrt_a(g.data, Rj, tmp.data, E->dim);
    }
    ann_f32 scale = (G->norm && k > 0) ? (1.0f / sqrtf((ann_f32)k)) : 1.0f;
    for (ann_usize d = 0; d < E->dim; d++)
      row[d] -= lr * scale * tmp.data[d];
  }
}

/* ========================= Dense + Optimizers ========================= */
ann_Dense ann_dense_new(ann_Arena *A, ann_usize in, ann_usize out,
                        ann_XRand *rng) {
  ann_Dense L = {0};
  L.in = in;
  L.out = out;
  L.W = (ann_f32 *)ann_arena_alloc(A, in * out * sizeof(ann_f32),
                                   alignof(ann_f32));
  L.b = (ann_f32 *)ann_arena_alloc(A, out * sizeof(ann_f32), alignof(ann_f32));
  ann_f32 scale = sqrtf(6.0f / (ann_f32)(in + out));
  for (ann_usize i = 0; i < in * out; i++)
    L.W[i] = (ann_xrand_uniform(rng) * 2.0f - 1.0f) * scale;
  for (ann_usize o = 0; o < out; o++)
    L.b[o] = 0.0f;
  L.momW = L.momB = L.mW = L.vW = L.mB = L.vB = NULL;
  return L;
}

ann_Tensor ann_dense_forward(ann_Arena *A, const ann_Dense *L, ann_Tensor x) {
  ann_Tensor y = ann_tensor_new(A, L->out);
  for (ann_usize o = 0; o < L->out; o++) {
    const ann_f32 *wrow = &L->W[o * L->in];
    y.data[o] = L->b[o] + ann_dot(wrow, x.data, L->in);
  }
  return y;
}

void ann_dense_opt_prepare(ann_Arena *A, ann_Dense *L, const ann_Optim *opt) {
  if (opt->kind == ANN_OPT_MOMENTUM) {
    if (!L->momW)
      L->momW = (ann_f32 *)ann_arena_alloc(A, L->in * L->out * sizeof(ann_f32),
                                           alignof(ann_f32));
    if (!L->momB)
      L->momB = (ann_f32 *)ann_arena_alloc(A, L->out * sizeof(ann_f32),
                                           alignof(ann_f32));
    for (ann_usize i = 0; i < L->in * L->out; i++)
      L->momW[i] = 0.0f;
    for (ann_usize o = 0; o < L->out; o++)
      L->momB[o] = 0.0f;
  } else if (opt->kind == ANN_OPT_ADAM) {
    if (!L->mW)
      L->mW = (ann_f32 *)ann_arena_alloc(A, L->in * L->out * sizeof(ann_f32),
                                         alignof(ann_f32));
    if (!L->vW)
      L->vW = (ann_f32 *)ann_arena_alloc(A, L->in * L->out * sizeof(ann_f32),
                                         alignof(ann_f32));
    if (!L->mB)
      L->mB = (ann_f32 *)ann_arena_alloc(A, L->out * sizeof(ann_f32),
                                         alignof(ann_f32));
    if (!L->vB)
      L->vB = (ann_f32 *)ann_arena_alloc(A, L->out * sizeof(ann_f32),
                                         alignof(ann_f32));
    for (ann_usize i = 0; i < L->in * L->out; i++) {
      L->mW[i] = 0.0f;
      L->vW[i] = 0.0f;
    }
    for (ann_usize o = 0; o < L->out; o++) {
      L->mB[o] = 0.0f;
      L->vB[o] = 0.0f;
    }
  }
}

static inline void ann_upd_sgd(ann_f32 *w, ann_f32 g, ann_f32 lr, ann_f32 l2) {
  *w -= lr * (g + l2 * (*w));
}

static inline void ann_upd_mom(ann_f32 *w, ann_f32 g, ann_f32 *v, ann_f32 lr,
                               ann_f32 l2, ann_f32 mu) {
  ann_f32 gg = g + l2 * (*w);
  *v = mu * (*v) - lr * gg;
  *w += *v;
}

static inline void ann_upd_adam(ann_f32 *w, ann_f32 g, ann_f32 *m, ann_f32 *v,
                                ann_f32 lr, ann_f32 l2, ann_f32 b1, ann_f32 b2,
                                ann_f32 eps, ann_u32 t) {
  ann_f32 gg = g + l2 * (*w);
  *m = b1 * (*m) + (1.0f - b1) * gg;
  *v = b2 * (*v) + (1.0f - b2) * gg * gg;
  ann_f32 mhat = (*m) / (1.0f - powf(b1, (ann_f32)t));
  ann_f32 vhat = (*v) / (1.0f - powf(b2, (ann_f32)t));
  *w -= lr * mhat / (sqrtf(vhat) + eps);
}

ann_f32 ann_dense_train_logistic(ann_Dense *L, ann_Tensor x, ann_f32 y_true,
                                 ann_Optim *opt) {
  ann_f32 z = L->b[0];
  for (ann_usize i = 0; i < L->in; i++)
    z += L->W[i] * x.data[i];
  ann_f32 yhat = ann_sigmoid(z);
  ann_f32 loss = ann_binary_ce(yhat, y_true);
  ann_f32 delta = (yhat - y_true);
  ++opt->t;
  for (ann_usize i = 0; i < L->in; i++) {
    ann_f32 g = delta * x.data[i];
    if (opt->kind == ANN_OPT_SGD)
      ann_upd_sgd(&L->W[i], g, opt->lr, opt->l2);
    else if (opt->kind == ANN_OPT_MOMENTUM)
      ann_upd_mom(&L->W[i], g, &L->momW[i], opt->lr, opt->l2, opt->mu);
    else
      ann_upd_adam(&L->W[i], g, &L->mW[i], &L->vW[i], opt->lr, opt->l2,
                   opt->beta1, opt->beta2, opt->eps, opt->t);
  }
  if (opt->kind == ANN_OPT_SGD)
    ann_upd_sgd(&L->b[0], delta, opt->lr, 0.0f);
  else if (opt->kind == ANN_OPT_MOMENTUM)
    ann_upd_mom(&L->b[0], delta, &L->momB[0], opt->lr, 0.0f, opt->mu);
  else
    ann_upd_adam(&L->b[0], delta, &L->mB[0], &L->vB[0], opt->lr, 0.0f,
                 opt->beta1, opt->beta2, opt->eps, opt->t);
  return loss;
}

ann_f32 ann_softmax_ce_from_logits_train(ann_Dense *L, ann_Tensor x,
                                         ann_usize y_true, ann_Optim *opt,
                                         ann_f32 *out_logits) {
  ann_usize C = L->out;
  ann_f32 zbuf[128];
  ann_f32 *z = (C <= 128) ? zbuf : (ann_f32 *)malloc(C * sizeof(ann_f32));
  for (ann_usize o = 0; o < C; o++) {
    const ann_f32 *wrow = &L->W[o * L->in];
    z[o] = L->b[o] + ann_dot(wrow, x.data, L->in);
  }
  ann_f32 loss = ann_softmax_ce_from_logits(z, C, y_true);
  ++opt->t;
  for (ann_usize o = 0; o < C; o++) {
    ann_f32 delta = z[o] - (o == y_true ? 1.0f : 0.0f);
    ann_f32 *wrow = &L->W[o * L->in];
    if (opt->kind == ANN_OPT_SGD) {
      for (ann_usize i = 0; i < L->in; i++)
        ann_upd_sgd(&wrow[i], delta * x.data[i], opt->lr, opt->l2);
      ann_upd_sgd(&L->b[o], delta, opt->lr, 0.0f);
    } else if (opt->kind == ANN_OPT_MOMENTUM) {
      for (ann_usize i = 0; i < L->in; i++)
        ann_upd_mom(&wrow[i], delta * x.data[i], &L->momW[o * L->in + i],
                    opt->lr, opt->l2, opt->mu);
      ann_upd_mom(&L->b[o], delta, &L->momB[o], opt->lr, 0.0f, opt->mu);
    } else {
      for (ann_usize i = 0; i < L->in; i++)
        ann_upd_adam(&wrow[i], delta * x.data[i], &L->mW[o * L->in + i],
                     &L->vW[o * L->in + i], opt->lr, opt->l2, opt->beta1,
                     opt->beta2, opt->eps, opt->t);
      ann_upd_adam(&L->b[o], delta, &L->mB[o], &L->vB[o], opt->lr, 0.0f,
                   opt->beta1, opt->beta2, opt->eps, opt->t);
    }
  }
  if (out_logits) {
    for (ann_usize o = 0; o < C; o++)
      out_logits[o] = z[o];
  }
  if (z != zbuf)
    free(z);
  return loss;
}

/* ========================= Quantized Dense ========================= */
ann_QDense ann_qdense_from_dense(ann_Arena *A, const ann_Dense *L) {
  ann_QDense Q = {0};
  Q.in = L->in;
  Q.out = L->out;
  Q.Wq = (int8_t *)ann_arena_alloc(A, L->in * L->out * sizeof(int8_t),
                                   alignof(int8_t));
  Q.scale =
      (ann_f32 *)ann_arena_alloc(A, L->out * sizeof(ann_f32), alignof(ann_f32));
  Q.b =
      (ann_f32 *)ann_arena_alloc(A, L->out * sizeof(ann_f32), alignof(ann_f32));
  for (ann_usize o = 0; o < L->out; o++) {
    const ann_f32 *wrow = &L->W[o * L->in];
    ann_f32 amax = 0.0f;
    for (ann_usize i = 0; i < L->in; i++) {
      ann_f32 a = fabsf(wrow[i]);
      if (a > amax)
        amax = a;
    }
    ann_f32 s = (amax > 0) ? amax / 127.0f : 1e-8f;
    Q.scale[o] = s;
    Q.b[o] = L->b[o];
    for (ann_usize i = 0; i < L->in; i++) {
      int q = (int)lrintf(wrow[i] / s);
      if (q > 127)
        q = 127;
      if (q < -128)
        q = -128;
      Q.Wq[o * L->in + i] = (int8_t)q;
    }
  }
  return Q;
}

ann_Tensor ann_qdense_forward(ann_Arena *A, const ann_QDense *Q, ann_Tensor x) {
  ann_Tensor y = ann_tensor_new(A, Q->out);
  for (ann_usize o = 0; o < Q->out; o++) {
    const int8_t *row = &Q->Wq[o * Q->in];
    ann_f32 s = Q->scale[o];
    ann_f32 acc = Q->b[o];
    for (ann_usize i = 0; i < Q->in; i++)
      acc += (ann_f32)row[i] * s * x.data[i];
    y.data[o] = acc;
  }
  return y;
}
