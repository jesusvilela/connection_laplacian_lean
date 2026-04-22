"""
Hand verification of L10/L11/L12 main theorems on n <= 4.

We build connection graphs G = (V, E, W) where V = [n], E is a set of
unordered pairs, and W ⊆ E are wrap edges. We check:

L10: charpoly(scalarLaplacian(orientationDoubleCover G))
     == charpoly(scalarLaplacian G) * charpoly(signedLaplacianMobius G).

L11: if G is a tree then every connected component is balanced.

L12: component C is balanced iff every closed walk within it has
     even number of wrap edges (checked for a finite basis of walks).
"""

import itertools
import numpy as np
from fractions import Fraction
from sympy import Matrix, Symbol, Poly, simplify

def scalar_laplacian(n, edges):
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for (u, v) in edges:
        L[u][u] += 1
        L[v][v] += 1
        L[u][v] -= 1
        L[v][u] -= 1
    return L

def signed_mobius(n, edges, wrap):
    """signedLaplacianMobius: off-diag wrap => +1, non-wrap => -1,
    diag => degree."""
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for (u, v) in edges:
        L[u][u] += 1
        L[v][v] += 1
        if (u, v) in wrap or (v, u) in wrap:
            L[u][v] += 1
            L[v][u] += 1
        else:
            L[u][v] -= 1
            L[v][u] -= 1
    return L

def orientation_double_cover(n, edges, wrap):
    """Vertices: (v, b) for v in [n], b in {0,1}.
    Edges: for each (u,v) in edges:
      if wrap: ((u,0),(v,1)), ((u,1),(v,0))
      else:    ((u,0),(v,0)), ((u,1),(v,1))
    Cover graph scalar Laplacian (ordinary graph Laplacian)."""
    N = 2 * n
    def idx(v, b): return 2 * v + b
    cover_edges = []
    for (u, v) in edges:
        if (u, v) in wrap or (v, u) in wrap:
            cover_edges.append((idx(u, 0), idx(v, 1)))
            cover_edges.append((idx(u, 1), idx(v, 0)))
        else:
            cover_edges.append((idx(u, 0), idx(v, 0)))
            cover_edges.append((idx(u, 1), idx(v, 1)))
    L = [[Fraction(0) for _ in range(N)] for _ in range(N)]
    for (a, b) in cover_edges:
        L[a][a] += 1
        L[b][b] += 1
        L[a][b] -= 1
        L[b][a] -= 1
    return L

def charpoly(M):
    return Matrix(M).charpoly()

def mat_list_to_sym(L):
    n = len(L)
    return Matrix(n, n, lambda i, j: L[i][j])

def components(n, edges):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    for (u, v) in edges:
        union(u, v)
    comp = {}
    for v in range(n):
        r = find(v)
        comp.setdefault(r, []).append(v)
    return list(comp.values())

def is_tree(n, edges):
    if n == 0:
        return False  # Mathlib IsTree requires Nonempty
    comps = components(n, edges)
    return len(comps) == 1 and len(edges) == n - 1

def is_balanced(n, edges, wrap, comp):
    """Balanced iff exists ε: V→Bool s.t. for every edge (u,v) with u ∈ comp,
    (edge is wrap) <=> ε(u) != ε(v)."""
    comp_set = set(comp)
    adj = {v: [] for v in comp_set}
    for (u, v) in edges:
        if u in comp_set:
            adj[u].append(v)
            adj[v].append(u)
    # BFS 2-color
    if not comp_set:
        return True
    root = comp[0]
    color = {root: 0}
    stack = [root]
    wrap_set = set()
    for (u, v) in wrap:
        wrap_set.add((u, v))
        wrap_set.add((v, u))
    while stack:
        u = stack.pop()
        for v in adj[u]:
            # edge u-v: is wrap?
            is_wrap = (u, v) in wrap_set
            expected = color[u] ^ (1 if is_wrap else 0)
            if v in color:
                if color[v] != expected:
                    return False
            else:
                color[v] = expected
                stack.append(v)
    return True

def enumerate_closed_walks(n, edges, wrap, v0, max_len):
    """Enumerate all walks from v0 to v0 of length <= max_len, return wrap counts."""
    adj = {v: [] for v in range(n)}
    wrap_set_local = set()
    for (u, v) in wrap:
        wrap_set_local.add((u, v))
        wrap_set_local.add((v, u))
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    results = []
    def walk(cur, length, wrap_count_sofar):
        if cur == v0 and length > 0:
            results.append(wrap_count_sofar)
        if length >= max_len:
            return
        for (nxt, ei) in adj[cur]:
            e = edges[ei]
            w = 1 if (e in wrap_set_local) else 0
            walk(nxt, length + 1, wrap_count_sofar + w)
    walk(v0, 0, 0)
    return results

def test_L10(n, edges, wrap):
    ws = set(wrap)
    L_scalar = scalar_laplacian(n, edges)
    L_mob = signed_mobius(n, edges, ws)
    L_cover = orientation_double_cover(n, edges, ws)
    cp_cover = charpoly(L_cover).as_expr()
    cp_scalar = charpoly(L_scalar).as_expr()
    cp_mob = charpoly(L_mob).as_expr()
    diff = simplify(cp_cover - cp_scalar * cp_mob)
    return diff == 0

def test_L11(n, edges, wrap):
    """If G is a tree then every component is balanced."""
    if not is_tree(n, edges):
        return None
    ws = set(wrap)
    comps = components(n, edges)
    return all(is_balanced(n, edges, ws, c) for c in comps)

def test_L12(n, edges, wrap, max_walk_len=8):
    """For each component, check: balanced <=> every closed walk even-wrap."""
    ws = set(wrap)
    comps = components(n, edges)
    results = []
    for c in comps:
        bal = is_balanced(n, edges, ws, c)
        # Check: for every v in c, every closed walk v~v has even wrap count
        even_closed = True
        for v in c:
            wcounts = enumerate_closed_walks(n, edges, wrap, v, max_walk_len)
            if any(w % 2 == 1 for w in wcounts):
                even_closed = False
                break
        results.append((c, bal, even_closed))
    return results

def all_graphs_up_to(n_max=4):
    """Generator over (n, edges) pairs for n <= n_max."""
    for n in range(1, n_max + 1):
        verts = list(range(n))
        pairs = list(itertools.combinations(verts, 2))
        for k in range(len(pairs) + 1):
            for esub in itertools.combinations(pairs, k):
                yield (n, list(esub))

def all_wraps(edges):
    for k in range(len(edges) + 1):
        for w in itertools.combinations(edges, k):
            yield list(w)

def main():
    l10_fails = []
    l11_fails = []
    l12_fails = []
    l10_count = 0
    l11_count = 0
    l12_count = 0

    for (n, edges) in all_graphs_up_to(4):
        for wrap in all_wraps(edges):
            # L10
            try:
                ok10 = test_L10(n, edges, wrap)
                l10_count += 1
                if not ok10:
                    l10_fails.append((n, edges, wrap))
            except Exception as e:
                l10_fails.append((n, edges, wrap, "error", repr(e)))

            # L11
            r11 = test_L11(n, edges, wrap)
            if r11 is not None:
                l11_count += 1
                if r11 is False:
                    l11_fails.append((n, edges, wrap))

            # L12
            r12 = test_L12(n, edges, wrap, max_walk_len=6)
            for (c, bal, even_closed) in r12:
                l12_count += 1
                if bal != even_closed:
                    l12_fails.append((n, edges, wrap, c, bal, even_closed))

    print(f"L10 tested: {l10_count}, fails: {len(l10_fails)}")
    for f in l10_fails[:5]: print("  ", f)
    print(f"L11 tested (trees): {l11_count}, fails: {len(l11_fails)}")
    for f in l11_fails[:5]: print("  ", f)
    print(f"L12 tested (components): {l12_count}, fails: {len(l12_fails)}")
    for f in l12_fails[:10]: print("  ", f)

if __name__ == "__main__":
    main()
