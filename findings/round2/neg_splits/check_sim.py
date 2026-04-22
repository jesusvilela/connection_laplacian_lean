"""
Second check: since both matrices are real symmetric with matching charpoly,
they are orthogonally similar. Verify by constructing P via Hadamard tensor.

Build P = I_V ⊗ R (Kronecker product of identity on V with Hadamard R = [[1,1],[1,-1]])
and test whether reindex(P * Ltilde * P^{-1}) equals fromBlocks. If yes on all
cases, strong evidence the theorem holds via the Hadamard construction hinted
in the proof sketch.
"""

import sympy as sp
from sympy import Matrix, zeros, eye, Rational

def scalar_lap(n, edges):
    M = zeros(n, n)
    for u, v in edges:
        M[u, v] -= 1
        M[v, u] -= 1
        M[u, u] += 1
        M[v, v] += 1
    return M

def signed_lap_mobius(n, edges, wrap):
    M = zeros(n, n)
    for (u, v) in edges:
        M[u, u] += 1
        M[v, v] += 1
        if frozenset((u, v)) in wrap:
            M[u, v] += 1
            M[v, u] += 1
        else:
            M[u, v] -= 1
            M[v, u] -= 1
    return M

def cover_lap_raw(n, edges, wrap):
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
    return scalar_lap(N, cover_edges)

def reindex_perm(n):
    # permutation matrix P: new index v -> old 2v, new index n+v -> old 2v+1
    N = 2 * n
    P = zeros(N, N)
    for v in range(n):
        P[v, 2 * v] = 1
        P[n + v, 2 * v + 1] = 1
    return P

def from_blocks(A, D):
    n = A.shape[0]
    m = D.shape[0]
    M = zeros(n + m, n + m)
    M[:n, :n] = A
    M[n:, n:] = D
    return M

def check_hadamard(name, n, edges, wrap):
    print(f"\n=== {name} ===")
    L = scalar_lap(n, edges)
    S = signed_lap_mobius(n, edges, wrap)
    Ltilde = cover_lap_raw(n, edges, wrap)
    Perm = reindex_perm(n)

    # Build Hadamard tensor: indexing (v, b) -> 2v + (0|1).
    # R = !![1,1;1,-1], we want P_had = I_V ⊗ R.
    R = Matrix([[1, 1], [1, -1]])
    Pkron = sp.kronecker_product(eye(n), R)
    # Its inverse: R^{-1} = (1/2) R; so P_kron^{-1} = I ⊗ (1/2 R)
    Pkron_inv = sp.kronecker_product(eye(n), Rational(1, 2) * R)

    conjugated = Pkron * Ltilde * Pkron_inv
    reindexed = Perm * conjugated * Perm.T
    block = from_blocks(L, S)

    # Note the Lean reindex sends (v,false) ↦ inl v, (v,true) ↦ inr v.
    # In our internal ordering (v,false) = 2v, (v,true) = 2v+1.
    # The Hadamard basis rotates (f, g) -> (f+g, f-g). The "false" sheet
    # in our coding maps to first basis vector of the 2-dim fiber.
    # With R = [[1,1],[1,-1]], R @ (a,b)^T = (a+b, a-b)^T, meaning
    # after conjugation new basis: row 0 = sym combination, row 1 = anti.
    # We want sym block to go to inl (first half) and anti to inr (second half).
    # The permutation we built sends (v,false) sheet to inl, which after Hadamard
    # is the sym combination. So we expect match with fromBlocks(L, S).

    eq = sp.simplify(reindexed - block)
    match = all(eq[i, j] == 0 for i in range(eq.shape[0]) for j in range(eq.shape[1]))
    print(f"  Ltilde (post Hadamard conj, reindexed):\n{reindexed}")
    print(f"  Expected fromBlocks(L,S):\n{block}")
    print(f"  MATCH with Hadamard P? {match}")
    if not match:
        print(f"  Diff:\n{eq}")
    # Check invertibility
    detP = Pkron.det()
    print(f"  det(P_hadamard) = {detP}")
    return match

results = []
results.append(check_hadamard("Ex1: K_2, no wrap", 2, [(0, 1)], set()))
results.append(check_hadamard("Ex2: K_2, wrap", 2, [(0, 1)], {frozenset((0, 1))}))
results.append(check_hadamard("Ex3: C_3, 1 wrap", 3,
    [(0, 1), (1, 2), (0, 2)], {frozenset((0, 1))}))
results.append(check_hadamard("Ex4: C_3, all wrap", 3,
    [(0, 1), (1, 2), (0, 2)],
    {frozenset((0, 1)), frozenset((1, 2)), frozenset((0, 2))}))
edges_k4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
results.append(check_hadamard("Ex5a: K_4, no wrap", 4, edges_k4, set()))
results.append(check_hadamard("Ex5b: K_4, 1 wrap", 4, edges_k4, {frozenset((0, 1))}))
results.append(check_hadamard("Ex5c: K_4, triangle wrap", 4, edges_k4,
    {frozenset((0, 1)), frozenset((1, 2)), frozenset((0, 2))}))
results.append(check_hadamard("Ex5d: K_4, all wrap", 4, edges_k4,
    set(frozenset(e) for e in edges_k4)))
results.append(check_hadamard("Ex6: P_3 middle wrap", 3,
    [(0, 1), (1, 2)], {frozenset((1, 2))}))
results.append(check_hadamard("Ex7: two K_2 first wrap", 4,
    [(0, 1), (2, 3)], {frozenset((0, 1))}))
results.append(check_hadamard("Ex8: C_4 two opp wrap", 4,
    [(0, 1), (1, 2), (2, 3), (0, 3)],
    {frozenset((0, 1)), frozenset((2, 3))}))
results.append(check_hadamard("Ex9: C_4 one wrap", 4,
    [(0, 1), (1, 2), (2, 3), (0, 3)], {frozenset((0, 1))}))

print(f"\n\n{'='*40}")
print(f"Summary: {sum(results)} / {len(results)} examples match via explicit Hadamard P.")
print(f"{'='*40}")
