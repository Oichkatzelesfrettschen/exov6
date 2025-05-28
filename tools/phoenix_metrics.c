#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <dirent.h>
#include <sys/stat.h>
#include <stdbool.h>

static bool has_suffix(const char *name, const char *suf) {
  size_t n = strlen(name), m = strlen(suf);
  return n >= m && strcmp(name + n - m, suf) == 0;
}

static int count_sloc_in_file(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f)
    return 0;
  int sloc = 0;
  bool in_block = false;
  char line[512];
  while (fgets(line, sizeof(line), f)) {
    char *p = line;
    while (isspace((unsigned char)*p))
      p++;
    if (*p == '\0')
      continue;
    if (in_block) {
      char *end = strstr(p, "*/");
      if (end)
        in_block = false;
      continue;
    }
    if (strncmp(p, "//", 2) == 0)
      continue;
    if (strncmp(p, "/*", 2) == 0) {
      if (!strstr(p + 2, "*/"))
        in_block = true;
      continue;
    }
    sloc++;
  }
  fclose(f);
  return sloc;
}

static int count_structs_in_file(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f)
    return 0;
  int count = 0;
  char line[512];
  while (fgets(line, sizeof(line), f)) {
    char *p = strstr(line, "struct ");
    if (p && strstr(p, "{"))
      count++;
  }
  fclose(f);
  return count;
}

static int count_simd_in_file(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f)
    return 0;
  int count = 0;
  char line[512];
  while (fgets(line, sizeof(line), f)) {
    if (strstr(line, "_mm") || strstr(line, "SIMD") || strstr(line, "sse") ||
        strstr(line, "avx") || strstr(line, "neon"))
      count++;
  }
  fclose(f);
  return count;
}

static void scan_dir(const char *dir, int *sloc, int *structs, int *simd) {
  DIR *d = opendir(dir);
  if (!d)
    return;
  struct dirent *ent;
  while ((ent = readdir(d))) {
    if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
      continue;
    char path[512];
    snprintf(path, sizeof(path), "%s/%s", dir, ent->d_name);
    struct stat st;
    if (stat(path, &st) < 0)
      continue;
    if (S_ISDIR(st.st_mode)) {
      scan_dir(path, sloc, structs, simd);
    } else if (has_suffix(ent->d_name, ".c") || has_suffix(ent->d_name, ".h")) {
      *sloc += count_sloc_in_file(path);
      *structs += count_structs_in_file(path);
      *simd += count_simd_in_file(path);
    }
  }
  closedir(d);
}

int main(int argc, char *argv[]) {
  const char *root = argc > 1 ? argv[1] : "kernel";
  double threshold = -1.0;
  if (argc > 2)
    threshold = atof(argv[2]);
  int sloc = 0, structs = 0, simd = 0;
  scan_dir(root, &sloc, &structs, &simd);
  double purity = sloc ? ((double)structs / (double)sloc) * 100.0 : 0.0;
  printf("SLOC:%d\nABSTRACTIONS:%d\nSIMD:%d\nPURITY:%.2f\n", sloc, structs,
         simd, purity);
  if (threshold >= 0.0 && purity < threshold) {
    fprintf(stderr, "Purity %.2f below threshold %.2f\n", purity, threshold);
    return 1;
  }
  return 0;
}
