"""
Sanity check for the refined Claim C1:
    for any non-wrap, non-bridge edge e of (G, W),
        beta(G, W) <= beta(G - e, W).

We test every non-iso graph on n <= 5, every wrap set,
every non-wrap non-bridge edge e.

Writes results.json next to this file and prints tau.
"""

from __future__ import annotations

import itertools
import json
from pathlib import Path

import networkx as nx


def edge_list(G):
    return [tuple(sorted(e)) for e in G.edges()]


def is_balanced_component(G, wrap):
    color = {}
    for comp in nx.connected_components(G):
        root = next(iter(comp))
        color[root] = 0
        stack = [root]
        while stack:
            u = stack.pop()
            for w in G.neighbors(u):
                e = tuple(sorted((u, w)))
                flip = 1 if e in wrap else 0
                expected = color[u] ^ flip
                if w not in color:
                    color[w] = expected
                    stack.append(w)
                elif color[w] != expected:
                    return False
    return True


def balanced_component_count(G, wrap):
    cnt = 0
    for comp in nx.connected_components(G):
        H = G.subgraph(comp).copy()
        H_edges = set(tuple(sorted(e)) for e in H.edges())
        wrap_H = wrap & H_edges
        if is_balanced_component(H, wrap_H):
            cnt += 1
    return cnt


def beta(G, W):
    return balanced_component_count(G, W)


def is_bridge(G, e):
    """Standard graph-theoretic bridge test (ignore wrap)."""
    u, v = e
    if not G.has_edge(u, v):
        return False
    H = G.copy()
    H.remove_edge(u, v)
    return not nx.has_path(H, u, v)


def all_labelled_graphs(n):
    nodes = list(range(n))
    potential = list(itertools.combinations(nodes, 2))
    for mask in range(1 << len(potential)):
        edges = [potential[i] for i in range(len(potential)) if mask & (1 << i)]
        G = nx.Graph()
        G.add_nodes_from(nodes)
        G.add_edges_from(edges)
        yield G


def all_graphs_iso(n):
    seen = []
    for G in all_labelled_graphs(n):
        for H in seen:
            if nx.is_isomorphic(G, H):
                break
        else:
            seen.append(G)
    return seen


def all_wrap_subsets(G):
    edges = edge_list(G)
    for r in range(len(edges) + 1):
        for sub in itertools.combinations(edges, r):
            yield frozenset(sub)


def main():
    tested = 0
    passed = 0
    counterexamples = []
    orig_c1_failures = 0  # failures of unrefined claim (bridges)
    total_edges_tried = 0

    for n in (3, 4, 5):
        for G in all_graphs_iso(n):
            for W in all_wrap_subsets(G):
                for e in edge_list(G):
                    if e in W:
                        continue  # skip wrap edges
                    total_edges_tried += 1
                    b_G = beta(G, W)
                    Ge = G.copy()
                    Ge.remove_edge(*e)
                    b_Ge = beta(Ge, W)
                    orig_ok = b_G >= b_Ge
                    if not orig_ok:
                        orig_c1_failures += 1
                    bridge = is_bridge(G, e)
                    if bridge:
                        continue  # refined claim only asks about non-bridges
                    tested += 1
                    # Refined claim: beta(G) <= beta(G - e)
                    # (i.e. removing a non-bridge non-wrap edge CANNOT decrease beta)
                    ok = b_G <= b_Ge
                    if ok:
                        passed += 1
                    else:
                        if len(counterexamples) < 10:
                            counterexamples.append({
                                "n": n,
                                "edges": edge_list(G),
                                "wrap": sorted(list(W)),
                                "removed_edge": list(e),
                                "beta_G": b_G,
                                "beta_G_minus_e": b_Ge,
                            })

    tau = passed / tested if tested else 0.0
    summary = {
        "claim": "beta(G) <= beta(G - e) for non-wrap non-bridge edge e",
        "envelope": "all non-iso graphs n in {3,4,5}, all wrap subsets",
        "tested": tested,
        "passed": passed,
        "tau": tau,
        "num_counterexamples": len(counterexamples),
        "counterexamples": counterexamples,
        "orig_c1_unrefined": {
            "total_nonwrap_edges_tried": total_edges_tried,
            "failures": orig_c1_failures,
            "note": "Failures of the UNrefined C1 (non-wrap edges including bridges).",
        },
    }

    out = Path(__file__).parent / "results.json"
    out.write_text(json.dumps(summary, indent=2))
    print(f"tested={tested}  passed={passed}  tau={tau:.6f}")
    print(f"orig-C1 failures (nonwrap, incl. bridges): {orig_c1_failures} / {total_edges_tried}")
    print(f"counterexamples to refined claim: {len(counterexamples)}")
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
