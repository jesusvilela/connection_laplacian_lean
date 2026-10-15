# -*- coding: utf-8 -*-
"""
independent_impl.py -- Independent reference implementation (numpy only) of
the Z/2 connection-Laplacian theory of

    paper/paper.tex
    "Kernel Dimension of the Z/2 Connection Laplacian on a Finite Simple
     Graph (A Formalisation in Lean 4 / Mathlib v4.11.0)"

The ONLY source of the definitions below is paper/paper.tex.  No Lean source
files and no previous fuzzer scripts were consulted while writing this
module; every convention is taken from the paper's displayed formulas, whose
line numbers (referring to paper/paper.tex) are quoted in the docstrings.

====================================================================== API ===

adj    : numpy n x n array with entries in {0,1}, symmetric, zero diagonal
         (adjacency matrix of the finite simple graph G; paper Sec. 2.1:
         "a (mathematically simple) graph" -- irreflexive, symmetric).
wrap_e : the wrap set W subset= E(G).  CANONICAL representation is a
         set of frozenset({u, v}) with u != v vertex indices.
         (Convenience, converted internally and validated against adj:
         a 0/1 symmetric zero-diagonal boolean adjacency matrix, or an
         iterable of 2-element tuples/sets, is also accepted.)
vertex indexing: 0 .. n-1.
Fibre indexing:   the paper's index sets are V x Fin2 (Sec. 3) and
         V x Bool = V~ (Def. 4.1).  Flat index of (u, i) is 2*u + i with
         i in {0,1}; for the cover we encode Bool by 0 = false = bot,
         1 = true = top (cf. Thm 4.4 which sends (v, bot) to the left and
         (v, top) to the right summand of V sqcup V).

Every function validates its inputs and raises ValueError on a wrap edge
that is not an edge of the graph (the paper requires W subset= E).

=================================================================== NOTES ===

Conventions implemented (all quoted from the paper):

* Phi(e) = sigma_x if e in W, I2 otherwise;  sigma_x = [[0,1],[1,0]]
  (paper.tex lines 135-143, Sec. 1).
* L_Mob (eq:connection-laplacian, paper.tex lines 144-153):
      L_Mob[u,v] = deg(u) * I2          if u = v,
                   -Phi({u,v})          if {u,v} in E,
                   0                    otherwise.
* L^sc (Sec. 2.3, lines 243-249):
      L^sc[u,v] = deg(u)  if u=v,  -1  if {u,v} in E,  0 otherwise.
* L^sg (Sec. 2.3, lines 251-260):
      L^sg[u,v] = deg(u)  if u=v,
                  +1      if {u,v} in E and {u,v} in W,
                  -1      if {u,v} in E and {u,v} not in W,
                  0       otherwise.
  (Confirmed by the sum-of-squares identity of Lemma 8.5, lines 1105-1113:
   <x, L^sg x> = sum_{E\\W} (x_u - x_v)^2 + sum_{W} (x_u + x_v)^2.)
* Cover adjacency (Def. 4.1, lines 380-391):
   (u,b) ~_G~ (v,c)  iff  {u,v} in E  and  ( {u,v} in W  <=>  b != c ).
* Balance (Def. 5.1, lines 556-566): component C is balanced iff there is
   eps : V -> Bool with, for every edge {u,v} of E inside C,
   {u,v} in W  <=>  eps(u) != eps(v).
   Remark 5.2 (lines 568-589): the definition is COMPONENT-LOCAL, and an
   isolated vertex is VACUOUSLY balanced.
* Fibre cardinality (Thm 5.3, lines 594-602): #pi0^{-1}(C) = 2 iff C
   balanced, else 1;  Cor. 5.7 (lines 700-709): #comp(G~) = #comp(G) + beta(G).

Author: independent audit implementation, round 8.
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "TOL", "I2", "SIGMA_X", "HADAMARD",
    "validate_adjacency", "normalise_wrap", "edges", "degrees",
    "scalar_laplacian", "signed_laplacian", "connection_laplacian",
    "flat_laplacian", "orientation_cover_adjacency",
    "spectrum", "kernel_dim", "connected_components",
    "is_balanced_component", "beta", "fibre_sheets", "cover_component_fibres",
]

#: Numerical tolerance used by kernel_dim (audit instruction: 1e-8).
TOL = 1e-8

#: 2x2 identity (the paper's I_2).
I2 = np.eye(2)

#: Pauli sigma_x = [[0,1],[1,0]]  (paper lines 141-143).
SIGMA_X = np.array([[0.0, 1.0],
                    [1.0, 0.0]])

#: Hadamard rotation R^ = [[1,1],[1,-1]] with R^ R^ = 2 I2
#: (paper eq. (Rhat), lines 226-234).
HADAMARD = np.array([[1.0, 1.0],
                     [1.0, -1.0]])


# --------------------------------------------------------------------- utils

def validate_adjacency(adj):
    """Validate and return `adj` as a float ndarray.

    Requirements (paper Sec. 2.1: mathematically simple graph):
    square, entries in {0,1}, symmetric, zero diagonal.
    """
    A = np.asarray(adj, dtype=float)
    if A.ndim != 2 or A.shape[0] != A.shape[1]:
        raise ValueError("adjacency must be a square n x n matrix")
    if A.size and not np.all((A == 0) | (A == 1)):
        raise ValueError("adjacency entries must be 0 or 1")
    if not np.array_equal(A, A.T):
        raise ValueError("adjacency must be symmetric (undirected graph)")
    if np.any(np.diag(A) != 0):
        raise ValueError("adjacency must be irreflexive (zero diagonal)")
    return A


def normalise_wrap(wrap_e, adj=None):
    """Canonicalise wrap data to a `set` of `frozenset({u, v})`.

    Accepted inputs: an iterable (set/list/tuple) of 2-element
    frozensets/sets/tuples of vertex indices, or a 0/1 symmetric
    zero-diagonal adjacency matrix (numpy array) marking the wrap edges.

    If `adj` is given, every wrap edge is checked to be an actual edge of
    the graph (the paper requires W subset= E; Sec. 2.1, line 215).
    """
    if wrap_e is None:
        return set()
    W = set()
    if isinstance(wrap_e, np.ndarray):
        M = validate_adjacency(wrap_e)
        n = M.shape[0]
        W = {frozenset((u, v)) for u in range(n) for v in range(u + 1, n)
             if M[u, v] == 1}
    elif isinstance(wrap_e, (set, frozenset, list, tuple)):
        for e in wrap_e:
            if isinstance(e, (frozenset, set, tuple, list)) and len(e) == 2:
                W.add(frozenset(int(x) for x in e))
            else:
                raise ValueError(
                    "wrap edge %r must be a 2-element set/tuple of vertices" % (e,))
    else:
        raise TypeError("wrap_e must be a set of frozenset({u,v}) edges "
                        "or a 0/1 adjacency matrix")
    if adj is not None:
        A = validate_adjacency(adj)
        n = A.shape[0]
        for e in W:
            u, v = sorted(e)
            if u == v or not (0 <= u < n and 0 <= v < n) or A[u, v] != 1:
                raise ValueError("wrap edge %s is not an edge of the graph "
                                 "(W must be a subset of E)" % (sorted(e),))
    return W


def edges(adj):
    """Edge list of the simple graph, as sorted frozensets {u,v} (u < v)."""
    A = validate_adjacency(adj)
    n = A.shape[0]
    return [frozenset((u, v)) for u in range(n) for v in range(u + 1, n)
            if A[u, v] == 1]


def degrees(adj):
    """Degree vector deg(u) = #{v : {u,v} in E} (paper Sec. 2.3)."""
    A = validate_adjacency(adj)
    return A.sum(axis=1)


def connected_components(adj):
    """Connected components pi_0(G) as a list of sorted vertex tuples
    (each tuple sorted ascending; components ordered by smallest vertex)."""
    A = validate_adjacency(adj)
    n = A.shape[0]
    seen = np.zeros(n, dtype=bool)
    comps = []
    for s in range(n):
        if seen[s]:
            continue
        stack = [s]
        seen[s] = True
        comp = []
        while stack:
            u = stack.pop()
            comp.append(u)
            for v in range(n):
                if A[u, v] == 1 and not seen[v]:
                    seen[v] = True
                    stack.append(v)
        comps.append(tuple(sorted(comp)))
    return comps


# --------------------------------------------------------------- Laplacians

def scalar_laplacian(adj):
    r"""Ordinary scalar Laplacian L^sc (paper Sec. 2.3, lines 243-249):

        L^sc[u,v] := deg(u)   if u = v,
                     -1       if {u,v} in E,
                     0        otherwise.

    ("i.e. Mathlib's SimpleGraph.lapMatrix", paper line 250.)
    """
    A = validate_adjacency(adj)
    return np.diag(A.sum(axis=1)) - A


def signed_laplacian(adj, wrap_e):
    r"""Signed (Mobius) Laplacian L^sg (paper Sec. 2.3, lines 251-260):

        L^sg[u,v] := deg(u)   if u = v,
                     +1       if {u,v} in E and {u,v} in W,   (wrap edges!)
                     -1       if {u,v} in E and {u,v} not in W,
                     0        otherwise.

    i.e. wrap edges contribute the OPPOSITE off-diagonal sign (+1) to
    non-wrap edges (-1).  This sign convention is pinned by the paper's
    quadratic-form identity (Lemma 8.5 / Sec. 2.3, lines 266-269):

        <x, L^sg x> = sum_{ {u,v} in E\W } (x_u - x_v)^2
                    + sum_{ {u,v} in W   } (x_u + x_v)^2 ,

    which the implementation cross-checks implicitly (PSD for all inputs).
    """
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    L = scalar_laplacian(A)
    for e in W:
        u, v = sorted(e)
        L[u, v] = 1.0
        L[v, u] = 1.0
    return L


def connection_laplacian(adj, wrap_e):
    r"""Z/2-connection (Mobius) Laplacian L_Mob
    (paper eq:connection-laplacian, Sec. 1, lines 144-153):

        L_Mob[u,v] := deg(u) * I2     if u = v,           (diagonal block)
                      -Phi({u,v})     if {u,v} in E,      (edge block)
                      0               otherwise,

        where  Phi(e) = sigma_x  if e in W,     sigma_x = [[0,1],[1,0]]
                       I2       if e notin W   (paper lines 135-143).

    Block placement: NON-WRAP edges carry the block  -I2 ;
                      WRAP edges carry the block     -sigma_x .
    The diagonal blocks are deg(u) * I2 in both cases.

    Index convention: rows/columns are (u, i) in V x Fin2, flattened as
    2*u + i (vertex-major, matching the paper's D (x) I2 ordering).
    """
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    n = A.shape[0]
    deg = A.sum(axis=1)
    L = np.zeros((2 * n, 2 * n))
    for u in range(n):
        L[2 * u, 2 * u] = deg[u]
        L[2 * u + 1, 2 * u + 1] = deg[u]
    for u in range(n):
        for v in range(u + 1, n):
            if A[u, v] == 1:
                block = SIGMA_X if frozenset((u, v)) in W else I2
                L[2 * u:2 * u + 2, 2 * v:2 * v + 2] = -block
                L[2 * v:2 * v + 2, 2 * u:2 * u + 2] = -block
    return L


def flat_laplacian(adj):
    r"""Flat Laplacian L_flat (paper lines 157-159): "obtained by the same
    recipe with Phi == I2, i.e. by ignoring the wrap structure; it agrees
    with two copies of the ordinary graph Laplacian", i.e.
    L_flat = kron(L^sc, I2).
    """
    return np.kron(scalar_laplacian(adj), I2)


def orientation_cover_adjacency(adj, wrap_e):
    r"""Adjacency of the orientation double cover G~
    (paper Def. 4.1, lines 380-391):

        vertex set  V~ = V x Bool  (flat index 2u + b; 0 = bot, 1 = top),
        (u,b) ~_G~ (v,c)  iff  {u,v} in E  and  ( {u,v} in W  <=>  b != c ).

    So: non-wrap edges of G connect SAME sheets (b = c), wrap edges
    connect OPPOSITE sheets (b != c).  The cover carries W~ = empty
    ("trivial connection", line 388).
    """
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    n = A.shape[0]
    T = np.zeros((2 * n, 2 * n))
    for u in range(n):
        for v in range(u + 1, n):
            if A[u, v] == 1:
                wrap = frozenset((u, v)) in W
                pairs = [(0, 1), (1, 0)] if wrap else [(0, 0), (1, 1)]
                for b, c in pairs:
                    T[2 * u + b, 2 * v + c] = 1.0
                    T[2 * v + c, 2 * u + b] = 1.0
    return T


# ----------------------------------------------------------------- spectrum

def spectrum(M):
    """Eigenvalues of the real symmetric matrix M, sorted ascending and
    rounded to 8 decimals (audit instruction: 1e-8)."""
    M = np.asarray(M, dtype=float)
    if M.size and not np.allclose(M, M.T, atol=1e-12):
        raise ValueError("spectrum() expects a symmetric matrix")
    vals = np.linalg.eigvalsh(M)
    return np.round(np.sort(vals), 8)


def kernel_dim(M, tol=TOL):
    """dim Ker M = #{ eigenvalues lambda with |lambda| <= tol }, tol = 1e-8
    (audit instruction).  Uses eigvalsh (all matrices here are real
    symmetric PSD by Lemma 8.5 / Thm 4.4)."""
    M = np.asarray(M, dtype=float)
    vals = np.linalg.eigvalsh(M)
    return int(np.sum(np.abs(vals) <= tol))


# ------------------------------------------------------------ combinatorics

def is_balanced_component(adj, wrap_e, comp):
    r"""The paper's balance criterion (Def. 5.1, lines 556-566):

    A connected component C is *balanced* iff there exists eps : V -> Bool
    such that for every edge {u,v} in E with both endpoints in C,

        {u,v} in W   <=>   eps(u) != eps(v).

    Convention notes (Remark 5.2, lines 568-589):
      * COMPONENT-LOCAL: only edges inside C are constrained; eps outside C
        is irrelevant -- so we compute eps on C only.
      * An ISOLATED VERTEX (no edges in C) is VACUOUSLY balanced.

    Implementation: root-labelled BFS/DFS, eps(root)=0 and
    eps(v) = eps(u) XOR 1_{ {u,v} in W } along search-tree edges; then the
    biconditional is checked on every edge inside C.  This decides the
    existential quantifier because any witness is determined up to a global
    flip by its value at the root.
    """
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    n = A.shape[0]
    comp = set(int(v) for v in comp)
    if not comp:
        raise ValueError("component must be non-empty")
    if not comp <= set(range(n)):
        raise ValueError("component vertices must be in range(n)")

    eps = {}
    for root in sorted(comp):          # loop handles non-connected input too
        if root in eps:
            continue
        eps[root] = 0
        stack = [root]
        while stack:
            u = stack.pop()
            for v in range(n):
                if v in comp and A[u, v] == 1 and v not in eps:
                    eps[v] = eps[u] ^ (1 if frozenset((u, v)) in W else 0)
                    stack.append(v)

    for u in comp:
        for v in comp:
            if u < v and A[u, v] == 1:
                is_wrap = frozenset((u, v)) in W
                if is_wrap != (eps[u] != eps[v]):
                    return False
    return True


def beta(adj, wrap_e):
    """beta(G) = #{balanced components of G} (paper Def. 5.1, lines 563-565,
    component-local count per Remark 5.2a)."""
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    return sum(1 for c in connected_components(A)
               if is_balanced_component(A, W, c))


def fibre_sheets(adj, wrap_e):
    r"""Per-component sheet count of the cover fibre and total.

    By Theorem 5.3 (thm:fiber-card, lines 594-602), for the projection
    pi : pi_0(G~) -> pi_0(G) induced by (v,b) |-> v,

        #pi^{-1}(C) = 2  if C is balanced,
                     1  otherwise,

    and by Corollary 5.7 (cor:components-cover, lines 700-709),

        #pi_0(G~) = #pi_0(G) + beta(G).

    Returns a dict:
        "components":               list of sorted vertex tuples (pi_0(G))
        "balanced":                 list of bools
        "sheets":                   list of ints in {1,2} (#pi^{-1}(C))
        "total_cover_components":   int, = sum(sheets) = #comp(G) + beta(G)
    """
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    comps = connected_components(A)
    balanced = [is_balanced_component(A, W, c) for c in comps]
    sheets = [2 if b else 1 for b in balanced]
    return {
        "components": comps,
        "balanced": balanced,
        "sheets": sheets,
        "total_cover_components": int(sum(sheets)),
    }


def cover_component_fibres(adj, wrap_e):
    r"""MEASURED fibre cardinalities: build the cover explicitly
    (Def. 4.1) and count, for each base component C, the connected
    components of G~ that project into C.  Returns (fibres, total) with
    fibres aligned with connected_components(adj).

    This is the construction-side measurement of Theorem 5.3 and is
    intentionally independent of the colouring predicate
    `is_balanced_component`: the two routes must agree (Thm 5.3).
    """
    A = validate_adjacency(adj)
    W = normalise_wrap(wrap_e, A)
    cover_comps = connected_components(orientation_cover_adjacency(A, W))
    base_comps = connected_components(A)
    fibres = []
    for bc in base_comps:
        bset = set(bc)
        cnt = 0
        for cc in cover_comps:
            proj = {v // 2 for v in cc}
            if proj <= bset and proj:      # projection is connected in G
                cnt += 1
        fibres.append(cnt)
    return fibres, len(cover_comps)
