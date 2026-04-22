"""Sanity probes to make sure the fuzzer is actually stressing things."""

import networkx as nx
import numpy as np

from fuzz import (
    cover_graph, is_balanced_component, rank_deficiency,
    scalar_laplacian, signed_laplacian_mobius, sorted_spectrum,
)


def probe(name, G, wrap):
    L_s = scalar_laplacian(G)
    L_m = signed_laplacian_mobius(G, wrap)
    H = cover_graph(G, wrap)
    L_t = scalar_laplacian(H)
    print(f"--- {name} ---")
    print(f"base components: {nx.number_connected_components(G)}")
    print(f"cover components: {nx.number_connected_components(H)}")
    print(f"spec L_tilde : {np.round(sorted_spectrum(L_t), 4).tolist()}")
    print(f"spec L_s + L_m : {np.round(np.sort(np.concatenate([sorted_spectrum(L_s), sorted_spectrum(L_m)])), 4).tolist()}")
    print(f"ker L_tilde = {rank_deficiency(L_t)}, "
          f"ker L_s = {rank_deficiency(L_s)}, "
          f"ker L_m = {rank_deficiency(L_m)}")
    for C in nx.connected_components(G):
        bal = is_balanced_component(G, wrap, frozenset(C))
        print(f"component {sorted(C)}: balanced={bal}")


# --- 3-cycle, no wrap
G = nx.cycle_graph(3)
wrap = {frozenset(e): False for e in G.edges()}
probe("C3 no wrap", G, wrap)

# --- 3-cycle, one wrap (odd wrap => unbalanced)
wrap = {frozenset(e): (e == (0, 1)) for e in G.edges()}
probe("C3 one wrap (unbalanced)", G, wrap)

# --- 4-cycle, two adjacent wraps (even total; balanced? depends on cocycle)
G = nx.cycle_graph(4)
wrap = {frozenset((0, 1)): True, frozenset((1, 2)): True,
        frozenset((2, 3)): False, frozenset((3, 0)): False}
probe("C4 two-adjacent wraps", G, wrap)

# --- K4 with one wrap
G = nx.complete_graph(4)
wrap = {frozenset(e): False for e in G.edges()}
wrap[frozenset((0, 1))] = True
probe("K4 with one wrap", G, wrap)

# --- Disconnected: K3 + isolated vertex
G = nx.Graph()
G.add_nodes_from(range(4))
G.add_edges_from([(0, 1), (1, 2), (2, 0)])
wrap = {frozenset((0, 1)): True, frozenset((1, 2)): False, frozenset((2, 0)): False}
probe("K3 + isolated, one wrap (unbalanced)", G, wrap)
