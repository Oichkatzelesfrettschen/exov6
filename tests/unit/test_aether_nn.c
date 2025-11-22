#include "aether_nn.h"
#include "test_framework.h"

#include <math.h>

TEST(aether_nn_basic) {
  enum { ARENA_BYTES = 64 * 1024 };
  unsigned char buf[ARENA_BYTES];
  ann_Arena arena;
  ann_arena_init(&arena, buf, ARENA_BYTES);

  ann_XRand rng = {.s = 1};
  ann_Embedding E = ann_embedding_new(&arena, 8, 4, &rng);
  ann_Aggregator G = ann_aggregator_new(&arena, ANN_AGG_SUM, 4, 4, 1, &rng);
  ann_usize idx[3] = {1, 2, 3};
  ann_Tensor v = ann_embedding_forward_agg(&arena, &E, idx, 3, &G);
  for (ann_usize i = 0; i < v.n; i++) {
    TEST_ASSERT(isfinite(v.data[i]));
  }

  ann_Dense D = ann_dense_new(&arena, 4, 1, &rng);
  ann_Optim opt = {
      .kind = ANN_OPT_SGD,
      .lr = 0.05f,
      .l2 = 0.0f,
      .t = 0,
  };
  ann_dense_opt_prepare(&arena, &D, &opt);

  for (int t = 0; t < 50; t++) {
    ann_dense_train_logistic(&D, v, 1.0f, &opt);
  }
  ann_Tensor y = ann_dense_forward(&arena, &D, v);
  float yhat = ann_sigmoid(y.data[0]);
  TEST_ASSERT(yhat >= 0.0f);
  TEST_ASSERT(yhat <= 1.0f);
}

TEST(aether_nn_optimizers) {
  enum { ARENA_BYTES = 64 * 1024 };
  unsigned char buf[ARENA_BYTES];
  ann_Arena arena;
  ann_arena_init(&arena, buf, ARENA_BYTES);
  ann_XRand rng = {.s = 2};

  /* Momentum optimizer initialisation and edge cases */
  ann_Dense Lm = ann_dense_new(&arena, 1, 1, &rng);
  ann_Optim mom = {
      .kind = ANN_OPT_MOMENTUM,
      .lr = 0.01f,
      .l2 = 0.0f,
      .mu = 0.9f,
      .t = 0,
  };
  ann_dense_opt_prepare(&arena, &Lm, &mom);
  TEST_ASSERT_NOT_NULL(Lm.momW);
  TEST_ASSERT_NOT_NULL(Lm.momB);
  TEST_ASSERT(fabsf(Lm.momW[0]) < 1e-6f);
  TEST_ASSERT(fabsf(Lm.momB[0]) < 1e-6f);

  mom.lr = 0.0f;
  ann_Tensor x = ann_tensor_new(&arena, 1);
  x.data[0] = 1.0f;
  ann_f32 w_before = Lm.W[0];
  ann_dense_train_logistic(&Lm, x, 1.0f, &mom);
  TEST_ASSERT(fabsf(Lm.W[0] - w_before) < 1e-6f);

  mom.lr = 0.1f;
  x.data[0] = 1e6f;
  ann_dense_train_logistic(&Lm, x, 0.0f, &mom);
  TEST_ASSERT(isfinite(Lm.W[0]));

  /* Adam optimizer initialisation and edge cases */
  ann_Dense La = ann_dense_new(&arena, 1, 1, &rng);
  ann_Optim adam = {
      .kind = ANN_OPT_ADAM,
      .lr = 0.001f,
      .l2 = 0.0f,
      .beta1 = 0.9f,
      .beta2 = 0.999f,
      .eps = 1e-8f,
      .t = 0,
  };
  ann_dense_opt_prepare(&arena, &La, &adam);
  TEST_ASSERT_NOT_NULL(La.mW);
  TEST_ASSERT_NOT_NULL(La.vW);
  TEST_ASSERT_NOT_NULL(La.mB);
  TEST_ASSERT_NOT_NULL(La.vB);
  TEST_ASSERT(fabsf(La.mW[0]) < 1e-6f);
  TEST_ASSERT(fabsf(La.vW[0]) < 1e-6f);
  TEST_ASSERT(fabsf(La.mB[0]) < 1e-6f);
  TEST_ASSERT(fabsf(La.vB[0]) < 1e-6f);

  adam.lr = 0.0f;
  ann_Tensor xa = ann_tensor_new(&arena, 1);
  xa.data[0] = 1.0f;
  w_before = La.W[0];
  ann_dense_train_logistic(&La, xa, 1.0f, &adam);
  TEST_ASSERT(fabsf(La.W[0] - w_before) < 1e-6f);

  adam.lr = 0.01f;
  xa.data[0] = 1e6f;
  ann_dense_train_logistic(&La, xa, 0.0f, &adam);
  TEST_ASSERT(isfinite(La.W[0]));
}

TEST_MAIN("aether_nn", test_aether_nn_basic, test_aether_nn_optimizers);
