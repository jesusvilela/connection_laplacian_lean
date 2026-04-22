"""
Negator: check if scalarLap_cover_splits could be FALSE for small graphs.

For a graph G on vertex set V with wrap edges W ⊆ E(G):

- scalarLap G is the ordinary graph Laplacian of G: deg on diagonal,
  -1 off-diagonal for every edge {u,v}.
- signedLaplacianMobius G: deg on diagonal, -1 for interior edges, +1 for wrap edges.
- coverGraph on V × Bool: (u,b)—(v,c) iff Adj u v and ((b=c) XOR wrap{u,v}).
  Explicitly: wrap edges flip sheet (b ≠ c), non-wrap keep (b = c).
- orientationDoubleCover.scalarLaplacian = coverGraph.lapMatrix (ordinary Laplacian of cover).

The theorem says: there exists invertible P with
    reindex(prodBoolEquivSum) (P * L̃ * P⁻¹) = fromBlocks(scalarLap, 0, 0, signedLap)
where prodBoolEquivSum : V × Bool ≃ V ⊕ V sends (v,false) ↦ inl v, (v,true) ↦ inr v.

Since reindex is a similarity by the permutation P_σ (from σ = prodBoolEquivSum),
the combined transformation is a similarity. Similarity preserves the characteristic
polynomial. So we check: charpoly(L̃) = charpoly(fromBlocks(scalarLap, 0, 0, signedLap))
                                        = charpoly(scalarLap) * charpoly(signedLap).
"""

import sympy as sp
from sympy import Matrix, zeros, Symbol, Poly, simplify, eye

def scalar_lap(V, edges):
    """Ordinary graph Laplacian: deg on diagonal, -1 for each edge."""
    n = len(V)
    M = zeros(n, n)
    for u, v in edges:
        M[u, v] -= 1
        M[v, u] -= 1
        M[u, u] += 1
        M[v, v] += 1
    return M

def signed_lap_mobius(V, edges, wrap):
    """Signed Laplacian: deg on diagonal, -1 for interior, +1 for wrap edges."""
    n = len(V)
    M = zeros(n, n)
    for (u, v) in edges:
        # degree contribution (independent of wrap)
        M[u, u] += 1
        M[v, v] += 1
        if frozenset((u, v)) in wrap:
            M[u, v] += 1
            M[v, u] += 1
        else:
            M[u, v] -= 1
            M[v, u] -= 1
    return M

def cover_lap(V, edges, wrap):
    """Ordinary Laplacian of the double cover graph.
    Vertex indexing: (v, b) for v in V, b in {False, True}.
    We order vertices as (v0,F),(v0,T),(v1,F),(v1,T),... i.e. pair by v first.
    Actually we'll use the order matching the Lean reindex:
    we will separately build it as-is and reindex by prodBoolEquivSum.

    Edges in cover: for each edge {u,v} with adj, connect
      (u,b)-(v,c) iff (b = c) XOR wrap{u,v}.
    wrap edges: (u,F)-(v,T) and (u,T)-(v,F)
    non-wrap:   (u,F)-(v,F) and (u,T)-(v,T)
    """
    n = len(V)
    # vertices of cover: list in order (v,False) then (v,True) grouped by v
    # We'll index as 2*v + (0 if False else 1)
    def idx(v, b):
        return 2 * v + (1 if b else 0)
    N = 2 * n
    cover_edges = []
    for (u, v) in edges:
        is_wrap = frozenset((u, v)) in wrap
        if is_wrap:
            cover_edges.append((idx(u, False), idx(v, True)))
            cover_edges.append((idx(u, True), idx(v, False)))
        else:
            cover_edges.append((idx(u, False), idx(v, False)))
            cover_edges.append((idx(u, True), idx(v, True)))
    return scalar_lap(list(range(N)), cover_edges), cover_edges

def reindex_prod_bool_to_sum(n):
    """Returns permutation taking internal order (v,F/T paired by v)
    to (inl v_0,..., inl v_{n-1}, inr v_0,..., inr v_{n-1}).
    prodBoolEquivSum: (v, false) -> inl v (index v in [0..n-1])
                      (v, true) -> inr v (index n+v in [0..2n-1])
    Our internal index: 2v (for F), 2v+1 (for T).
    So permutation sigma : new index -> old index
        new index v (0 <= v < n, inl v)   -> old index 2v
        new index n+v (inr v)              -> old index 2v+1
    """
    N = 2 * n
    P = zeros(N, N)
    for v in range(n):
        # new row v corresponds to old row 2v
        P[v, 2 * v] = 1
        # new row n+v corresponds to old row 2v+1
        P[n + v, 2 * v + 1] = 1
    return P

def from_blocks(A, zero_UR, zero_LL, D):
    n = A.shape[0]
    m = D.shape[0]
    M = zeros(n + m, n + m)
    M[:n, :n] = A
    M[n:, n:] = D
    return M

def check(name, V, edges, wrap):
    print(f"\n=== {name} ===")
    print(f"  V = {V}, edges = {edges}, wrap = {[list(e) for e in wrap]}")
    n = len(V)
    L = scalar_lap(V, edges)
    S = signed_lap_mobius(V, edges, wrap)
    Ltilde_raw, _ = cover_lap(V, edges, wrap)
    # Reindex Ltilde_raw through prodBoolEquivSum
    P = reindex_prod_bool_to_sum(n)
    # reindex: rows and cols permuted -> P * Ltilde_raw * P^T
    Ltilde_reindexed = P * Ltilde_raw * P.T
    block = from_blocks(L, None, None, S)

    x = Symbol('x')
    cp_Ltilde = (x * sp.eye(2 * n) - Ltilde_raw).det()
    cp_Ltilde = sp.expand(cp_Ltilde)
    cp_block = (x * sp.eye(2 * n) - block).det()
    cp_block = sp.expand(cp_block)
    cp_L = (x * sp.eye(n) - L).det()
    cp_S = (x * sp.eye(n) - S).det()
    cp_L = sp.expand(cp_L)
    cp_S = sp.expand(cp_S)
    print(f"  scalarLap:\n{L}")
    print(f"  signedLap:\n{S}")
    print(f"  Ltilde (cover Lap, raw order 2v,2v+1):\n{Ltilde_raw}")
    print(f"  Ltilde (reindexed):\n{Ltilde_reindexed}")
    print(f"  fromBlocks:\n{block}")
    print(f"  charpoly(Ltilde)      = {cp_Ltilde}")
    print(f"  charpoly(fromBlocks)  = {cp_block}")
    print(f"  charpoly(L)*charpoly(S) = {sp.expand(cp_L * cp_S)}")
    match = sp.simplify(cp_Ltilde - cp_block) == 0
    print(f"  MATCH charpolys? {match}")
    if not match:
        print(f"  *** COUNTEREXAMPLE: theorem may be FALSE here ***")
    else:
        # Also check: does reindex alone (without a rotation P) already match?
        direct = (Ltilde_reindexed == block)
        print(f"  reindexed(Ltilde) == fromBlocks directly? {direct}")
    return match


# Example 1: 2 vertices, 1 edge, not wrap
check("Ex1: K_2, no wrap", [0, 1], [(0, 1)], set())

# Example 2: 2 vertices, 1 edge, wrap
check("Ex2: K_2, wrap", [0, 1], [(0, 1)], {frozenset((0, 1))})

# Example 3: 3-cycle, 1 wrap edge, 2 non-wrap
check("Ex3: C_3, 1 wrap", [0, 1, 2],
      [(0, 1), (1, 2), (0, 2)],
      {frozenset((0, 1))})

# Example 4: 3-cycle, 3 wrap edges
check("Ex4: C_3, all wrap", [0, 1, 2],
      [(0, 1), (1, 2), (0, 2)],
      {frozenset((0, 1)), frozenset((1, 2)), frozenset((0, 2))})

# Example 5a: K_4, no wrap
edges_k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
check("Ex5a: K_4, no wrap", [0, 1, 2, 3], edges_k4, set())

# Example 5b: K_4, 1 wrap edge
check("Ex5b: K_4, 1 wrap", [0, 1, 2, 3], edges_k4, {frozenset((0, 1))})

# Example 5c: K_4, 3 wrap edges forming a triangle
check("Ex5c: K_4, wrap triangle 0-1-2", [0, 1, 2, 3], edges_k4,
      {frozenset((0, 1)), frozenset((1, 2)), frozenset((0, 2))})

# Example 5d: K_4, all wrap
check("Ex5d: K_4, all wrap", [0, 1, 2, 3], edges_k4,
      set(frozenset(e) for e in edges_k4))

# Example 6: Path graph P_3 with wrap on middle edge
check("Ex6: P_3 (0-1-2), middle wrap", [0, 1, 2],
      [(0, 1), (1, 2)],
      {frozenset((1, 2))})

# Example 7: disconnected 2 edges, one wrap one not
check("Ex7: two disjoint K_2, first wrap", [0, 1, 2, 3],
      [(0, 1), (2, 3)],
      {frozenset((0, 1))})

# Example 8: C_4 with 2 opposite wrap edges
check("Ex8: C_4, 2 opposite wrap", [0, 1, 2, 3],
      [(0, 1), (1, 2), (2, 3), (0, 3)],
      {frozenset((0, 1)), frozenset((2, 3))})

# Example 9: C_4 with 1 wrap edge (odd wrap parity)
check("Ex9: C_4, 1 wrap", [0, 1, 2, 3],
      [(0, 1), (1, 2), (2, 3), (0, 3)],
      {frozenset((0, 1))})
