#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "libos/posix.h"

struct dl_handle {
  void *base;
  size_t size;
};

struct mod_hdr {
  char magic[4];
  uint32_t count;
};

struct mod_sym {
  char name[16];
  uint32_t off;
};

static void write_sample_module(const char *path) {
  struct mod_hdr hdr = {"MOD0", 1};
  struct mod_sym sym = {"message", 0x1c};
  FILE *f = fopen(path, "wb");
  assert(f);
  fwrite(&hdr, 1, sizeof(hdr), f);
  fwrite(&sym, 1, sizeof(sym), f);
  fwrite("hello", 1, 6, f);
  fclose(f);
}

void *libos_dlopen(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f)
    return NULL;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  void *buf = malloc(sz);
  if (!buf) {
    fclose(f);
    return NULL;
  }
  if (fread(buf, 1, sz, f) != (size_t)sz) {
    free(buf);
    fclose(f);
    return NULL;
  }
  fclose(f);
  struct dl_handle *h = malloc(sizeof(*h));
  h->base = buf;
  h->size = sz;
  return h;
}

void *libos_dlsym(void *handle, const char *name) {
  struct dl_handle *h = handle;
  struct {
    char magic[4];
    uint32_t count;
  } *hdr = h->base;
  struct {
    char name[16];
    uint32_t off;
  } *sym = (void *)(hdr + 1);
  if (memcmp(hdr->magic, "MOD0", 4) != 0)
    return NULL;
  for (uint32_t i = 0; i < hdr->count; i++, sym++)
    if (strcmp(sym->name, name) == 0 && sym->off < h->size)
      return (char *)h->base + sym->off;
  return NULL;
}

int libos_dlclose(void *handle) {
  struct dl_handle *h = handle;
  if (!h)
    return -1;
  free(h->base);
  free(h);
  return 0;
}

int main(void) {
  const char *path = "sample_mod.bin";
  write_sample_module(path);
  void *h = libos_dlopen(path);
  assert(h);
  const char *msg = libos_dlsym(h, "message");
  assert(msg);
  assert(strcmp(msg, "hello") == 0);
  assert(libos_dlclose(h) == 0);
  remove(path);
  return 0;
}
