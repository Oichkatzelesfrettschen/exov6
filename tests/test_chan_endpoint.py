import pathlib, subprocess, tempfile, textwrap

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <stddef.h>

typedef struct {unsigned int id;} exo_cap;
typedef struct {
  size_t msg_size;
} msg_type_desc;
typedef struct {
  size_t msg_size;
  const msg_type_desc *desc;
} chan_t;

int chan_endpoint_send(chan_t *c, exo_cap dest, const void *msg, size_t len) {
  (void)dest;
  if (!c || len != c->msg_size)
    return -1;
  return 0;
}
int chan_endpoint_recv(chan_t *c, exo_cap src, void *msg, size_t len) {
  (void)src;
  (void)msg;
  if (!c || len != c->msg_size)
    return -1;
  return 0;
}

int main(void) {
  msg_type_desc d = {sizeof(int)};
  chan_t c = {d.msg_size, &d};
  int m = 5;
  assert(chan_endpoint_send(&c, (exo_cap){0}, &m, sizeof(m)) == 0);
  unsigned char bad = 0;
  assert(chan_endpoint_send(&c, (exo_cap){0}, &bad, sizeof(bad)) < 0);
  return 0;
}
    """
)


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(C_CODE)
        subprocess.check_call(["gcc", "-std=c11", str(src), "-o", str(exe)])
        subprocess.check_call([str(exe)])


def test_chan_endpoint_validation():
    compile_and_run()
