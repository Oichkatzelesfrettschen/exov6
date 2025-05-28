#ifndef NSTR_GRAPH_H
#define NSTR_GRAPH_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct nstr_graph nstr_graph;

nstr_graph* nstr_graph_open(void);
void nstr_graph_close(nstr_graph* g);
int nstr_graph_add_edge(nstr_graph* g, int from, int to);
int nstr_graph_remove_edge(nstr_graph* g, int from, int to);
int nstr_graph_query(nstr_graph* g, int from, int to);

#ifdef __cplusplus
}
#endif

#endif /* NSTR_GRAPH_H */
