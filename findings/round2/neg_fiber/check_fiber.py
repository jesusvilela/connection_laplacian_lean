"""
Brute-force test of the fiber cardinality formula:

  |{D in pi0(coverGraph) : componentProj D = C}| == (2 if isBalanced C else 1)

For each small graph + wrap subset + component:
  - compute coverGraph via: (u,b)~(v,c) iff Adj(u,v) and ( (b==c) iff not wrap(uv) )
  - compute pi0(coverGraph) (via networkx connected_components)
  - for each component C of G, count cover-components whose vertex-fst-projection
    yields C
  - determine isBalanced(C) by brute-forcing eps : V -> {0,1} over C-vertices,
    checking consistency on edges with an endpoint in C.
    (Per Lean def: the quantifier is "for all u,v with Adj u v and u in C" —
    which forces v to also be in C by connectedness of graphs; an edge in C
    has both endpoints in C.)
  - compare formula vs actual fiber size; log counterexamples.
"""

from __future__ import annotations
import itertools
import networkx as nx


def build_cover(V, edges, wrap):
    """edges: list of frozensets {u,v}. wrap: set of frozensets (subset of edges)."""
    Gtilde = nx.Graph()
    for v in V:
        for b in (0, 1):
            Gtilde.add_node((v, b))
    for e in edges:
        u, v = tuple(e)
        is_wrap = e in wrap
        # (u,b) ~ (v,c) iff ((b == c) iff not wrap)
        for b in (0, 1):
            for c in (0, 1):
                same_sheet = (b == c)
                cond = (same_sheet == (not is_wrap))
                if cond:
                    Gtilde.add_edge((u, b), (v, c))
    return Gtilde


def build_base(V, edges):
    G = nx.Graph()
    for v in V:
        G.add_node(v)
    for e in edges:
        u, v = tuple(e)
        G.add_edge(u, v)
    return G


def components_of(G):
    return [frozenset(c) for c in nx.connected_components(G)]


def is_balanced(C_vertices, edges_in_C, wrap):
    """C_vertices: set. edges_in_C: list of edges (frozenset) whose endpoints lie in C_vertices.
       Brute force eps: C_vertices -> {0,1} (fix one vertex to 0 to break symmetry)."""
    if not C_vertices:
        return True
    verts = list(C_vertices)
    v0 = verts[0]
    # eps(v0) = 0; try all assignments to remaining
    others = verts[1:]
    for bits in itertools.product((0, 1), repeat=len(others)):
        eps = {v0: 0}
        for v, b in zip(others, bits):
            eps[v] = b
        ok = True
        for e in edges_in_C:
            u, v = tuple(e)
            is_wrap = e in wrap
            want = (eps[u] != eps[v])
            if is_wrap != want:
                ok = False
                break
        if ok:
            return True
    return False


def fiber_counts(V, edges, wrap):
    """Return list of (C, fiber_size, balanced) over base components C."""
    base = build_base(V, edges)
    cov = build_cover(V, edges, wrap)
    base_comps = components_of(base)
    cov_comps = components_of(cov)
    out = []
    for C in base_comps:
        # edges in C
        edges_in_C = [e for e in edges if any(v in C for v in e)]
        # for a simple graph with an edge {u,v}, both are in same component if one is
        edges_in_C = [e for e in edges_in_C if all(v in C for v in e)]
        bal = is_balanced(C, edges_in_C, wrap)
        # count cover components D whose fst-projection equals C
        fib = 0
        for D in cov_comps:
            proj = frozenset(v for (v, b) in D)
            if proj == C:
                fib += 1
        expected = 2 if bal else 1
        out.append((C, fib, bal, expected))
    return out


def test_graph(label, V, edges, wrap_subsets=None):
    edges = [frozenset(e) for e in edges]
    if wrap_subsets is None:
        # enumerate all subsets of edges
        wrap_subsets = []
        for r in range(len(edges) + 1):
            for s in itertools.combinations(edges, r):
                wrap_subsets.append(frozenset(s))
    counterexamples = []
    tested = 0
    for wrap in wrap_subsets:
        tested += 1
        res = fiber_counts(V, edges, wrap)
        for (C, fib, bal, expected) in res:
            if fib != expected:
                counterexamples.append({
                    "label": label,
                    "V": list(V),
                    "edges": [tuple(sorted(e)) for e in edges],
                    "wrap": [tuple(sorted(e)) for e in wrap],
                    "C": sorted(C),
                    "fib": fib,
                    "balanced": bal,
                    "expected": expected,
                })
    return tested, counterexamples


def main():
    print("=" * 70)
    print("Fiber-cardinality formula brute-force checker")
    print("=" * 70)
    all_ce = []

    tests = []

    # 1. single edge
    tests.append(("single edge K_2", [0, 1], [(0, 1)]))
    # 2. P_3 (path 3)
    tests.append(("path P_3", [0, 1, 2], [(0, 1), (1, 2)]))
    # 3. C_3
    tests.append(("cycle C_3", [0, 1, 2], [(0, 1), (1, 2), (2, 0)]))
    # 4. C_4
    tests.append(("cycle C_4", [0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)]))
    # 5. C_5
    tests.append(("cycle C_5", list(range(5)),
                  [(i, (i + 1) % 5) for i in range(5)]))
    # 6. K_4
    tests.append(("K_4", [0, 1, 2, 3], [(i, j) for i in range(4) for j in range(i+1, 4)]))
    # 7. K_{3,3}
    bi_edges = [(i, j) for i in [0, 1, 2] for j in [3, 4, 5]]
    tests.append(("K_{3,3}", [0, 1, 2, 3, 4, 5], bi_edges))
    # 8. Petersen (brute-force wrap subsets limited: too many, sample)
    # 9. theta graph (two vertices joined by 3 internally disjoint paths of length 2)
    tests.append(("theta graph", [0, 1, 2, 3, 4],
                  [(0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 1)]))
    # 10. disjoint union C_3 + C_3
    tests.append(("C_3 + C_3 (disjoint)", [0, 1, 2, 3, 4, 5],
                  [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]))
    # 11. tree (star K_{1,4})
    tests.append(("star K_{1,4}", [0, 1, 2, 3, 4],
                  [(0, 1), (0, 2), (0, 3), (0, 4)]))
    # 12. isolated vertex + edge
    tests.append(("isolated + edge", [0, 1, 2], [(0, 1)]))
    # 13. bowtie (two triangles glued at vertex)
    tests.append(("bowtie", [0, 1, 2, 3, 4],
                  [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)]))
    # 14. K_4 minus an edge
    tests.append(("K_4 - e", [0, 1, 2, 3],
                  [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]))
    # 15. cube graph Q_3
    cube_V = list(range(8))
    cube_E = []
    for x in range(8):
        for bit in (1, 2, 4):
            y = x ^ bit
            if x < y:
                cube_E.append((x, y))
    tests.append(("cube Q_3", cube_V, cube_E))

    total_counts = 0
    for (label, V, E) in tests:
        # skip exhaustive wrap enum when |E| too large (Q_3 has 12 edges -> 4096 subsets ok; K_{3,3} has 9 -> 512 ok)
        tested, ces = test_graph(label, V, E, wrap_subsets=None)
        total_counts += tested
        status = "OK" if not ces else f"COUNTEREXAMPLES: {len(ces)}"
        print(f"[{label}] |V|={len(V)} |E|={len(E)} tested {tested} wrap-subsets: {status}")
        if ces:
            all_ce.extend(ces)
            # show first 2
            for ce in ces[:2]:
                print(f"   - {ce}")

    # 16. Petersen sampled
    pet_V = list(range(10))
    pet_E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
             (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
             (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    # Sample random wrap subsets
    import random
    random.seed(42)
    sampled_wraps = []
    edges_pet = [frozenset(e) for e in pet_E]
    for _ in range(5000):
        mask = random.getrandbits(len(edges_pet))
        w = frozenset(edges_pet[i] for i in range(len(edges_pet)) if (mask >> i) & 1)
        sampled_wraps.append(w)
    tested, ces = test_graph("Petersen (sampled 5000)", pet_V, pet_E, wrap_subsets=sampled_wraps)
    total_counts += tested
    status = "OK" if not ces else f"COUNTEREXAMPLES: {len(ces)}"
    print(f"[Petersen sampled] tested {tested}: {status}")
    if ces:
        all_ce.extend(ces)
        for ce in ces[:2]:
            print(f"   - {ce}")

    print("=" * 70)
    print(f"TOTAL graph/wrap configs tested: {total_counts}")
    print(f"TOTAL counterexamples: {len(all_ce)}")

    if all_ce:
        print("FIRST COUNTEREXAMPLE:")
        print(all_ce[0])
    else:
        print("Formula HELD across all tested configurations.")


if __name__ == "__main__":
    main()
