import networkx as nx

def test_lattice_complex_dag():
    g = nx.DiGraph()
    g.add_nodes_from(['a','b','c','d','e'])
    g.add_edge('a','b')
    g.add_edge('a','c')
    g.add_edge('b','d')
    g.add_edge('c','d')
    g.add_edge('d','e')
    assert nx.is_directed_acyclic_graph(g)
