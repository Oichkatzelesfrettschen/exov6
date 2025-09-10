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

TEST_MAIN("aether_nn", test_aether_nn_basic);
