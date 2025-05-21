/*
 * rcrs - restartable driver supervisor
 *
 * This user-level helper reads command lines from /drivers.conf and
 * keeps the specified programs running.  Each non-empty line in the
 * configuration file represents one driver.  Lines beginning with '#'
 * are treated as comments.  When a driver process exits the supervisor
 * automatically restarts it.
 *
 * Example configuration:
 *   kbdserv
 *   otherdriver arg1 arg2
 */
#include "fcntl.h"
#include "stat.h"
#include "types.h"
#include "user.h"

#define MAX_DRIVERS 8
#define MAX_ARGS 8
#define MAX_LINE 128

struct driver {
  char *argv[MAX_ARGS];
  char *buf; // backing storage for argv strings
  int pid;
};

static int parse_config(const char *path, struct driver *d, int max) {
  int fd, n, idx = 0;
  char line[MAX_LINE];

  fd = open(path, O_RDONLY);
  if (fd < 0)
    return -1;

  int pos = 0;
  char c;
  while (idx < max && (n = read(fd, &c, 1)) == 1) {
    if (c == '\n' || pos == MAX_LINE - 1) {
      line[pos] = '\0';
      pos = 0;

      // trim leading whitespace
      char *p = line;
      while (*p == ' ' || *p == '\t')
        p++;
      if (*p == '\0' || *p == '#')
        continue;

      d[idx].buf = malloc(strlen(p) + 1);
      if (!d[idx].buf)
        break;
      strcpy(d[idx].buf, p);

      int arg = 0;
      char *q = d[idx].buf;
      while (arg < MAX_ARGS - 1) {
        while (*q == ' ' || *q == '\t')
          q++;
        if (*q == '\0')
          break;
        d[idx].argv[arg++] = q;
        while (*q && *q != ' ' && *q != '\t')
          q++;
        if (*q == '\0')
          break;
        *q++ = '\0';
      }
      d[idx].argv[arg] = 0;
      idx++;
    } else {
      line[pos++] = c;
    }
  }
  close(fd);
  return idx;
}

static int start_driver(struct driver *d) {
  int pid = fork();
  if (pid == 0) {
    exec(d->argv[0], d->argv);
    exit();
  }
  return pid;
}

int main(void) {
  struct driver drv[MAX_DRIVERS];
  memset(drv, 0, sizeof(drv));
  int n = parse_config("drivers.conf", drv, MAX_DRIVERS);
  if (n <= 0)
    exit();

  for (int i = 0; i < n; i++)
    drv[i].pid = start_driver(&drv[i]);

  for (;;) {
    int pid = wait();
    if (pid < 0)
      continue;
    for (int i = 0; i < n; i++) {
      if (drv[i].pid == pid) {
        drv[i].pid = start_driver(&drv[i]);
        break;
      }
    }
  }
  return 0;
}
