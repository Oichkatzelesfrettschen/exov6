#include "nstr_graph.h"
#include <stdlib.h>
#include <pthread.h>

/** Internal representation of a single node. */
struct node {
  int id;            /**< Numeric identifier of the node. */
  struct node *next; /**< Next node in the list. */
};

/** Linked list item representing one directed edge. */
struct edge {
  int from;          /**< Source node identifier. */
  int to;            /**< Destination node identifier. */
  struct edge *next; /**< Next edge in the list. */
};

/** Opaque graph implementation details. */
struct nstr_graph {
  struct node *nodes;   /**< Linked list of nodes. */
  struct edge *edges;   /**< Linked list of edges. */
  pthread_mutex_t lock; /**< Protects concurrent access. */
};

/**
 * Locate a node by its identifier.
 *
 * @param g   Graph instance to search.
 * @param id  Identifier of the node.
 * @return Pointer to the node or NULL if not found.
 */
static struct node *find_node(struct nstr_graph *g, int id) {
  struct node *n = g->nodes;
  while (n) {
    if (n->id == id)
      return n;
    n = n->next;
  }
  return 0;
}

/**
 * Ensure a node with the given identifier exists in the graph.
 *
 * @param g   Graph to modify.
 * @param id  Identifier of the node to add.
 */
static void add_node(struct nstr_graph *g, int id) {
  if (find_node(g, id))
    return;
  struct node *n = malloc(sizeof(*n));
  if (!n)
    return;
  n->id = id;
  n->next = g->nodes;
  g->nodes = n;
}

/**
 * Create a new empty graph instance.
 *
 * @return Newly allocated graph or NULL on allocation failure.
 */
nstr_graph *nstr_graph_open(void) {
  struct nstr_graph *g = malloc(sizeof(*g));
  if (!g)
    return 0;
  g->nodes = 0;
  g->edges = 0;
  pthread_mutex_init(&g->lock, NULL);
  return g;
}

void nstr_graph_close(nstr_graph *g) {
  if (!g)
    return;
  pthread_mutex_lock(&g->lock);
  struct edge *e = g->edges;
  while (e) {
    struct edge *next = e->next;
    free(e);
    e = next;
  }
  struct node *n = g->nodes;
  while (n) {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  pthread_mutex_unlock(&g->lock);
  pthread_mutex_destroy(&g->lock);
  free(g);
}

int nstr_graph_add_edge(nstr_graph *g, int from, int to) {
  if (!g)
    return -1;
  pthread_mutex_lock(&g->lock);
  add_node(g, from);
  add_node(g, to);
  struct edge *e = g->edges;
  while (e) {
    if (e->from == from && e->to == to) {
      pthread_mutex_unlock(&g->lock);
      return 0;
    }
    e = e->next;
  }
  e = malloc(sizeof(*e));
  if (!e) {
    pthread_mutex_unlock(&g->lock);
    return -1;
  }
  e->from = from;
  e->to = to;
  e->next = g->edges;
  g->edges = e;
  pthread_mutex_unlock(&g->lock);
  return 0;
}

int nstr_graph_remove_edge(nstr_graph *g, int from, int to) {
  if (!g)
    return -1;
  pthread_mutex_lock(&g->lock);
  struct edge **prev = &g->edges;
  while (*prev) {
    if ((*prev)->from == from && (*prev)->to == to) {
      struct edge *tmp = *prev;
      *prev = tmp->next;
      free(tmp);
      pthread_mutex_unlock(&g->lock);
      return 0;
    }
    prev = &(*prev)->next;
  }
  pthread_mutex_unlock(&g->lock);
  return -1;
}

int nstr_graph_query(nstr_graph *g, int from, int to) {
  if (!g)
    return 0;
  pthread_mutex_lock(&g->lock);
  struct edge *e = g->edges;
  while (e) {
    if (e->from == from && e->to == to) {
      pthread_mutex_unlock(&g->lock);
      return 1;
    }
    e = e->next;
  }
  pthread_mutex_unlock(&g->lock);
  return 0;
}
