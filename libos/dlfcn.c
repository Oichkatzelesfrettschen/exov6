#include "libos/libfs.h"
#include "file.h"
#include "posix.h"
#include "stat.h"
#include <stdlib.h>
#include <string.h>

struct dl_handle {
  void *base;
  size_t size;
};

void *libos_dlopen(const char *path) {
  struct file *f = libfs_open(path, 0);
  if (!f)
    return 0;
  struct stat st;
  if (filestat(f, &st) < 0) {
    libfs_close(f);
    return 0;
  }
  void *buf = malloc(st.size);
  if (!buf) {
    libfs_close(f);
    return 0;
  }
  int n = libfs_read(f, buf, st.size);
  libfs_close(f);
  if (n != (int)st.size) {
    free(buf);
    return 0;
  }
  struct dl_handle *h = malloc(sizeof(*h));
  if (!h) {
    free(buf);
    return 0;
  }
  h->base = buf;
  h->size = st.size;
  return h;
}

struct mod_hdr {
  char magic[4];
  uint32_t count;
};
struct mod_sym {
  char name[16];
  uint32_t off;
};

void *libos_dlsym(void *handle, const char *symbol) {
  if (!handle)
    return 0;
  struct dl_handle *h = handle;
  struct mod_hdr *hdr = h->base;
  if (memcmp(hdr->magic, "MOD0", 4) != 0)
    return 0;
  struct mod_sym *sym = (struct mod_sym *)(hdr + 1);
  for (uint32_t i = 0; i < hdr->count; i++, sym++) {
    if (strcmp(sym->name, symbol) == 0 && sym->off < h->size)
      return (char *)h->base + sym->off;
  }
  return 0;
}

int libos_dlclose(void *handle) {
  if (!handle)
    return -1;
  struct dl_handle *h = handle;
  free(h->base);
  free(h);
  return 0;
}
