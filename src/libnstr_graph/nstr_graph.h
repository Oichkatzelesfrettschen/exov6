#ifndef NSTR_GRAPH_H
#define NSTR_GRAPH_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct nstr_graph nstr_graph;

/**
 * @brief Allocate a new empty graph instance.
 *
 * @return Pointer to the newly allocated graph or NULL on failure.
 */
nstr_graph *nstr_graph_open(void);

/**
 * @brief Destroy a graph and free all associated resources.
 *
 * @param g Graph to close. NULL is allowed and will be ignored.
 */
void nstr_graph_close(nstr_graph *g);

/**
 * @brief Add a directed edge to the graph.
 *
 * Missing nodes are created automatically.
 *
 * @param g    Graph to modify.
 * @param from Source node identifier.
 * @param to   Destination node identifier.
 *
 * @return 0 on success, -1 on allocation failure.
 */
int nstr_graph_add_edge(nstr_graph *g, int from, int to);

/**
 * @brief Remove a directed edge from the graph.
 *
 * @param g    Graph to modify.
 * @param from Source node identifier.
 * @param to   Destination node identifier.
 *
 * @return 0 on success, -1 if the edge does not exist.
 */
int nstr_graph_remove_edge(nstr_graph *g, int from, int to);

/**
 * @brief Query whether an edge exists between two nodes.
 *
 * @param g    Graph to inspect.
 * @param from Source node identifier.
 * @param to   Destination node identifier.
 *
 * @return 1 if the edge exists, 0 otherwise.
 */
int nstr_graph_query(nstr_graph *g, int from, int to);

#ifdef __cplusplus
}
#endif

#endif /* NSTR_GRAPH_H */
