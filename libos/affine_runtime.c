
#include "affine_runtime.h"
#include "ulib.h" // for malloc/free

// Allocate an affine channel
EXO_NODISCARD affine_chan_t *
affine_chan_create(const struct msg_type_desc *desc) {
  affine_chan_t *c = malloc(sizeof(affine_chan_t));
  if (c) {
    c->base.desc = desc;
    c->base.msg_size = msg_desc_size(desc);
    c->used_send = 0;
    c->used_recv = 0;
  }
  return c;
}

// Destroy an affine channel
void affine_chan_destroy(affine_chan_t *c) { free(c); }

// Send once through the channel
EXO_NODISCARD int affine_chan_send(affine_chan_t *c, exo_cap dest,
                                   const void *msg, size_t len) {
  if (!c || c->used_send)
    return -1;
  int r = chan_endpoint_send(&c->base, dest, msg, len);
  if (r == 0)
    c->used_send = 1;
  return r;
}

// Receive once through the channel
EXO_NODISCARD int affine_chan_recv(affine_chan_t *c, exo_cap src, void *msg,
                                   size_t len) {
  if (!c || c->used_recv)
    return -1;
  int r = chan_endpoint_recv(&c->base, src, msg, len);
  if (r == 0)
    c->used_recv = 1;
  return r;
}

// Execute a lambda term with resource accounting
int lambda_run(lambda_term_t *t, int fuel) {
  if (!t || !t->fn)
    return -1;
  int ret = 0;
  while (fuel-- > 0 && ret == 0) {
    ret = t->fn(t->env);
    t->steps++;
  }
  return ret;
}

// Lambda capability helpers
lambda_cap_t *lambda_cap_create(lambda_fn fn, void *env, exo_cap cap) {
  lambda_cap_t *lc = malloc(sizeof(lambda_cap_t));
  if (lc) {
    lc->term.fn = fn;
    lc->term.env = env;
    lc->term.steps = 0;
    lc->cap = cap;
    lc->consumed = 0;
  }
  return lc;
}

void lambda_cap_destroy(lambda_cap_t *lc) { free(lc); }

int lambda_cap_use(lambda_cap_t *lc, int fuel) {
  if (!lc || lc->consumed)
    return -1;
  int r = lambda_run(&lc->term, fuel);
  lc->consumed = 1;
  return r;
}

int lambda_cap_delegate(lambda_cap_t *lc, uint16_t new_owner) {
  if (!lc || lc->consumed)
    return -1;
  (void)new_owner; // ownership metadata handled by kernel
  return cap_inc(lc->cap.id);
}

int lambda_cap_revoke(lambda_cap_t *lc) {
  if (!lc || lc->consumed)
    return -1;
  int r = cap_revoke(lc->cap.id);
  if (r == 0)
    lc->consumed = 1;
  return r;
}
