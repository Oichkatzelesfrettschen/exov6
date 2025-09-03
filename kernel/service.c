#include <types.h>
#include "defs.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "service.h"
#include <string.h>

/** Maximum number of services that can be registered. */
#define MAX_SERVICES 32
/** Maximum number of dependencies per service. */
#define MAX_DEPS 4

/** Entry representing a registered service. */
typedef struct service_entry {
  char name[16];                        /**< Service identifier. */
  char path[64];                        /**< Executable path for restart. */
  struct proc *proc;                    /**< Owning process. */
  struct service_entry *deps[MAX_DEPS]; /**< Dependency references. */
  int dep_count;                        /**< Number of dependencies. */
  bool auto_restart;                    /**< Restart on failure. */
} service_entry_t;

static struct {
  struct spinlock lock;                  /**< Protects the table. */
  service_entry_t entries[MAX_SERVICES]; /**< Stored services. */
} service_table = {0};

__attribute__((constructor)) static void service_init(void) {
  initlock(&service_table.lock, "services");
}

/** Find a service entry by name. */
static service_entry_t *find_service(const char *name) {
  for (int i = 0; i < MAX_SERVICES; ++i) {
    if (service_table.entries[i].name[0] &&
        strncmp(service_table.entries[i].name, name,
                sizeof(service_table.entries[i].name)) == 0)
      return &service_table.entries[i];
  }
  return NULL;
}

/** Locate a process by pid. */
static struct proc *proc_by_pid(int pid) {
  for (struct proc *p = ptable.proc; p < &ptable.proc[NPROC]; ++p)
    if (p->pid == pid)
      return p;
  return NULL;
}

/** Spawn a new instance of the service. */
static void restart_service(service_entry_t *s) {
  int pid = fork();
  if (pid == 0) {
    char *argv[] = {s->path, NULL};
    exec(s->path, argv);
    exit();
  } else if (pid > 0) {
    s->proc = proc_by_pid(pid);
  }
}

int service_register(const char *name, const char *path,
                     service_options_t opts) {
  struct proc *cur = myproc();
  acquire(&service_table.lock);
  for (int i = 0; i < MAX_SERVICES; ++i) {
    service_entry_t *e = &service_table.entries[i];
    if (e->name[0] == 0) {
      strncpy(e->name, name, sizeof(e->name) - 1);
      strncpy(e->path, path, sizeof(e->path) - 1);
      e->proc = cur;
      e->auto_restart = opts.auto_restart;
      e->dep_count = 0;
      release(&service_table.lock);
      return 0;
    }
  }
  release(&service_table.lock);
  return -1;
}

int service_add_dependency(const char *name, const char *dependency) {
  acquire(&service_table.lock);
  service_entry_t *svc = find_service(name);
  service_entry_t *dep = find_service(dependency);
  if (!svc || !dep || svc->dep_count >= MAX_DEPS) {
    release(&service_table.lock);
    return -1;
  }
  svc->deps[svc->dep_count++] = dep;
  release(&service_table.lock);
  return 0;
}

/** Called when a process exits to handle restart logic. */
void service_notify_exit(struct proc *p) {
  acquire(&service_table.lock);
  for (int i = 0; i < MAX_SERVICES; ++i) {
    service_entry_t *e = &service_table.entries[i];
    if (e->proc == p) {
      e->proc = NULL;
      if (e->auto_restart)
        restart_service(e);
      break;
    }
  }
  release(&service_table.lock);
}
