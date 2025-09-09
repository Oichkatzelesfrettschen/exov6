/*
 * rcrs - restartable driver supervisor
 *
 * This user-level helper reads command lines from drivers.conf and
 * keeps the specified programs running.  Each non-empty line in the
 * configuration file represents one driver.  Lines beginning with '#'
 * are treated as comments.  When a driver process exits the supervisor
 * automatically restarts it.
 *
 * Example configuration:
 *   kbdserv
 *   pingdriver
 */
#include "fcntl.h"
#include "sys/stat.h"
#include "types.h"
#include "user.h"
#include "ipc.h"
#include "libos/driver.h"

#define PING 1
#define PONG 2
#define PING_DELAY 20
#define DEFAULT_TIMEOUT (PING_DELAY * 2)
#define STATUS_INTERVAL 200
#define MAX_DRIVERS 8
#define MAX_ARGS 8
#define MAX_LINE 128

struct driver {
  char *argv[MAX_ARGS];
  char *buf; // backing storage for argv strings
  int pid;
  uint last_ping;
  int awaiting_pong;
  int ping_timeout;
  int restarts;
};

static int starts_with(const char *s, const char *p) {
  while (*p) {
    if (*s++ != *p++)
      return 0;
  }
  return 1;
}

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

      d[idx].ping_timeout = 0;
      int arg = 0;
      char *q = d[idx].buf;
      while (arg < MAX_ARGS - 1) {
        while (*q == ' ' || *q == '\t')
          q++;
        if (*q == '\0')
          break;
        char *tok = q;
        while (*q && *q != ' ' && *q != '\t')
          q++;
        if (*q)
          *q++ = '\0';

        if (starts_with(tok, "--timeout="))
          d[idx].ping_timeout = atoi(tok + 10);
        else
          d[idx].argv[arg++] = tok;
      }
      d[idx].argv[arg] = 0;
      if (d[idx].ping_timeout <= 0)
        d[idx].ping_timeout = DEFAULT_TIMEOUT;
      idx++;
    } else {
      line[pos++] = c;
    }
  }
  close(fd);
  return idx;
}

static int start_driver(struct driver *d) {
  return driver_spawn(d->argv[0], d->argv);
}

int main(void) {
  struct driver drv[MAX_DRIVERS];
  memset(drv, 0, sizeof(drv));
  int n = parse_config("drivers.conf", drv, MAX_DRIVERS);
  if (n <= 0)
    exit(0);

  int p[2];
  if (pipe(p) < 0)
    exit(0);

  if (fork() == 0) {
    close(p[0]);
    for (;;) {
      zipc_msg_t m;
      if (endpoint_recv(&m) == 0)
        write(p[1], &m, sizeof(m));
    }
    return 0;
  }

  close(p[1]);
  fcntl(p[0], F_SETFL, O_NONBLOCK);

  for (int i = 0; i < n; i++) {
    drv[i].pid = start_driver(&drv[i]);
    drv[i].awaiting_pong = 0;
    drv[i].last_ping = uptime();
    drv[i].restarts = 0;
  }

  uint last_report = uptime();

  for (;;) {
    uint now = uptime();

    for (int i = 0; i < n; i++) {
      if (!drv[i].awaiting_pong && now - drv[i].last_ping >= PING_DELAY) {
        zipc_msg_t m = {0};
        m.w0 = PING;
        m.w1 = i;
        endpoint_send(&m);
        drv[i].last_ping = now;
        drv[i].awaiting_pong = 1;
      }
    }

    zipc_msg_t m;
    while (read(p[0], &m, sizeof(m)) == sizeof(m)) {
      if (m.w0 == PONG && m.w1 < (uint)n)
        drv[m.w1].awaiting_pong = 0;
    }

    now = uptime();
    for (int i = 0; i < n; i++) {
      if (drv[i].awaiting_pong && now - drv[i].last_ping > (uint)drv[i].ping_timeout) {
        printf(1, "rcrs: restarting %s\n", drv[i].argv[0]);
        kill(drv[i].pid);
        wait();
        drv[i].pid = start_driver(&drv[i]);
        drv[i].awaiting_pong = 0;
        drv[i].last_ping = now;
        drv[i].restarts++;
      }
    }

    if (now - last_report >= STATUS_INTERVAL) {
      printf(1, "rcrs status:\n");
      for (int i = 0; i < n; i++) {
        printf(1, "  %s pid %d %s restarts %d\n", drv[i].argv[0], drv[i].pid,
               drv[i].awaiting_pong ? "waiting" : "alive", drv[i].restarts);
      }
      last_report = now;
    }
  }
  return 0;
}
