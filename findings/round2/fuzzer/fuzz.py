"""
Round-2 fuzzer for the three sorry'd claims in connection_laplacian_lean.

Targets
-------
T1  scalarLap_cover_splits     (L5_Cover.lean:176)
    ∃ invertible P,  reindex( P · L̃ · P⁻¹ ) = fromBlocks(scalarLap, 0, 0, signedLapMobius)
    Necessary-condition check: spectrum(L̃) == spectrum(scalarLap) ⊔ spectrum(signedLapMobius)
                               det, trace, char-poly all match.
T2  scalarLap_cover_kernel_dim (L5_Cover.lean:199)
    dim ker(L̃) = dim ker(scalarLap) + dim ker(signedLapMobius).

T3  componentProj_fiber_card   (L6_Cohomology.lean:104)
    For each component C of G:
        #{ D ∈ π₀(coverGraph) : proj D = C } = (2 if balanced C else 1).

Enumeration
-----------
All simple graphs on n = 2..5 vertices (up to isomorphism, via nauty geng
or NetworkX's atlas / per-n generator) × all 2^|E| wrap subsets.

Author: fuzzer role, Round-2 multi-agent audit.
"""

from __future__ import annotations

import itertools
import json
import math
import os
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterable

import networkx as nx
import numpy as np

TOL = 1e-8


# ------------------------------------------------------------------ graphs

def all_graphs_up_to_iso(n: int) -> Iterable[nx.Graph]:
    """All simple graphs on {0,..,n-1} up to isomorphism.

    Enumerate every edge subset on n vertices; filter isomorphic duplicates
    with a canonical-form map (WL hash is cheap and sufficient at n<=5).
    """
    seen: set[str] = set()
    verts = list(range(n))
    all_edges = list(itertools.combinations(verts, 2))
    for r in range(len(all_edges) + 1):
        for es in itertools.combinations(all_edges, r):
            G = nx.Graph()
            G.add_nodes_from(verts)
            G.add_edges_from(es)
            h = nx.weisfeiler_lehman_graph_hash(G, iterations=4)
            # WL hash collisions at n<=5 are rare but possible; dedupe with
            # an actual iso test inside the hash bucket.
            bucket_key = h
            if bucket_key in seen:
                # already have one representative with this hash; check if
                # the new graph is genuinely isomorphic to a stored rep.
                is_new = True
                for rep in _iso_bucket[bucket_key]:
                    if nx.is_isomorphic(G, rep):
                        is_new = False
                        break
                if is_new:
                    _iso_bucket[bucket_key].append(G)
                    yield G
            else:
                seen.add(bucket_key)
                _iso_bucket[bucket_key].append(G)
                yield G


_iso_bucket: dict[str, list[nx.Graph]] = defaultdict(list)


# ------------------------------------------------------------------ laplacians

def scalar_laplacian(G: nx.Graph) -> np.ndarray:
    n = G.number_of_nodes()
    L = np.zeros((n, n))
    for u, v in G.edges():
        L[u, v] = -1.0
        L[v, u] = -1.0
    for v in G.nodes():
        L[v, v] = G.degree(v)
    return L


def signed_laplacian_mobius(G: nx.Graph, wrap: dict[frozenset, bool]) -> np.ndarray:
    """Wrap edges contribute +1 off-diagonal; non-wrap contribute -1.
    Diagonal = degree.
    """
    n = G.number_of_nodes()
    L = np.zeros((n, n))
    for u, v in G.edges():
        e = frozenset({u, v})
        val = 1.0 if wrap[e] else -1.0
        L[u, v] = val
        L[v, u] = val
    for v in G.nodes():
        L[v, v] = G.degree(v)
    return L


def cover_graph(G: nx.Graph, wrap: dict[frozenset, bool]) -> nx.Graph:
    """Orientation double cover.

    Vertex set V x {0,1}; edge (u,b)-(v,c) iff Adj u v AND
    (wrap{u,v} ↔ b ≠ c).
    Encode (v, b) as 2*v + b.
    """
    n = G.number_of_nodes()
    H = nx.Graph()
    H.add_nodes_from(range(2 * n))
    for u, v in G.edges():
        e = frozenset({u, v})
        if wrap[e]:
            # wrap: sheets flip
            H.add_edge(2 * u + 0, 2 * v + 1)
            H.add_edge(2 * u + 1, 2 * v + 0)
        else:
            # non-wrap: sheets preserved
            H.add_edge(2 * u + 0, 2 * v + 0)
            H.add_edge(2 * u + 1, 2 * v + 1)
    return H


# ------------------------------------------------------------------ balance

def is_balanced_component(
    G: nx.Graph, wrap: dict[frozenset, bool], component: frozenset[int]
) -> bool:
    """Brute-force: exist 2-coloring ε : V -> {0,1} s.t. for every edge {u,v}
    with u ∈ component, wrap{u,v} ↔ ε(u) ≠ ε(v).

    Because we only constrain edges whose u ∈ component, and wrap is symmetric,
    we scan over 2^|component| colorings on that component (vertices outside
    don't enter any constraint through this component's edges, since edges have
    both endpoints in the same component).

    Edge {u,v} with u ∈ C means v ∈ C (C is a connected component), so we can
    restrict to colorings of C.
    """
    comp_vs = sorted(component)
    comp_edges = [
        (u, v) for (u, v) in G.edges()
        if u in component  # equivalently v in component
    ]
    for bits in range(1 << len(comp_vs)):
        eps = {v: (bits >> i) & 1 for i, v in enumerate(comp_vs)}
        ok = True
        for u, v in comp_edges:
            w = wrap[frozenset({u, v})]
            differ = eps[u] != eps[v]
            if w != differ:
                ok = False
                break
        if ok:
            return True
    return False


# ------------------------------------------------------------------ checks

def rank_deficiency(M: np.ndarray) -> int:
    """n - rank(M) via SVD with a robust tolerance."""
    if M.size == 0:
        return 0
    s = np.linalg.svd(M, compute_uv=False)
    if s.size == 0:
        return M.shape[0]
    tol = max(M.shape) * s.max() * np.finfo(float).eps * 10
    return int(np.sum(s <= tol))


def sorted_spectrum(M: np.ndarray) -> np.ndarray:
    vals = np.linalg.eigvalsh(M)  # symmetric
    return np.sort(vals)


def specs_match(a: np.ndarray, b: np.ndarray) -> bool:
    if a.shape != b.shape:
        return False
    return bool(np.allclose(a, b, atol=1e-7))


# ------------------------------------------------------------------ driver

def run_case(G: nx.Graph, wrap_bits: int, edges_canonical: list[tuple[int, int]]):
    """Return a dict of (passed, detail) per target or None for the config."""
    wrap = {
        frozenset({u, v}): bool((wrap_bits >> i) & 1)
        for i, (u, v) in enumerate(edges_canonical)
    }
    L_scalar = scalar_laplacian(G)
    L_signed = signed_laplacian_mobius(G, wrap)
    H = cover_graph(G, wrap)
    L_tilde = scalar_laplacian(H)

    # T1: spectrum equality (necessary condition for similarity to block sum).
    spec_tilde = sorted_spectrum(L_tilde)
    spec_union = np.sort(np.concatenate([sorted_spectrum(L_scalar),
                                          sorted_spectrum(L_signed)]))
    t1_ok = specs_match(spec_tilde, spec_union)
    t1_detail = None
    if not t1_ok:
        t1_detail = {
            "spec_tilde": spec_tilde.tolist(),
            "spec_union": spec_union.tolist(),
            "trace_tilde": float(np.trace(L_tilde)),
            "trace_union": float(np.trace(L_scalar) + np.trace(L_signed)),
            "det_tilde": float(np.linalg.det(L_tilde)),
            "det_union": float(np.linalg.det(L_scalar) * np.linalg.det(L_signed)),
        }

    # T2: kernel dimensions add.
    k_tilde = rank_deficiency(L_tilde)
    k_scalar = rank_deficiency(L_scalar)
    k_signed = rank_deficiency(L_signed)
    t2_ok = (k_tilde == k_scalar + k_signed)
    t2_detail = None
    if not t2_ok:
        t2_detail = {
            "k_tilde": k_tilde,
            "k_scalar": k_scalar,
            "k_signed": k_signed,
        }

    # T3: fiber cardinalities.
    base_components = [frozenset(c) for c in nx.connected_components(G)]
    cover_components = [frozenset(c) for c in nx.connected_components(H)]

    # Fiber: cover components whose projection (first coord / 2) lands in C.
    t3_ok = True
    t3_detail = []
    for C in base_components:
        fib = 0
        for D in cover_components:
            proj = {d // 2 for d in D}
            # Cover component D maps into one base component via proj.
            # By coverProj, proj(D) ⊆ some base component; check it equals C.
            # Actually it suffices to check proj(D) is a subset of C.
            if proj and proj.issubset(C):
                fib += 1
        bal = is_balanced_component(G, wrap, C)
        expect = 2 if bal else 1
        if fib != expect:
            t3_ok = False
            t3_detail.append({
                "component": sorted(C),
                "balanced": bal,
                "fiber": fib,
                "expected": expect,
            })

    return {
        "T1": (t1_ok, t1_detail),
        "T2": (t2_ok, t2_detail),
        "T3": (t3_ok, t3_detail if t3_detail else None),
    }


def graph_descr(G: nx.Graph) -> str:
    return f"n={G.number_of_nodes()},E={sorted(G.edges())}"


def run_all(ns=(2, 3, 4, 5)):
    totals = {"configs": 0, "graphs": 0}
    fails = {"T1": [], "T2": [], "T3": []}

    for n in ns:
        _iso_bucket.clear()
        gcount = 0
        for G in all_graphs_up_to_iso(n):
            gcount += 1
            edges_canonical = sorted(tuple(sorted(e)) for e in G.edges())
            m = len(edges_canonical)
            for wrap_bits in range(1 << m):
                totals["configs"] += 1
                result = run_case(G, wrap_bits, edges_canonical)
                for t in ("T1", "T2", "T3"):
                    ok, det = result[t]
                    if not ok:
                        fails[t].append({
                            "graph": graph_descr(G),
                            "wrap_bits": wrap_bits,
                            "wrap_edges": [
                                e for i, e in enumerate(edges_canonical)
                                if (wrap_bits >> i) & 1
                            ],
                            "detail": det,
                        })
        print(f"n={n}: {gcount} non-iso graphs, cumulative configs={totals['configs']}",
              flush=True)
        totals["graphs"] += gcount

    return totals, fails


if __name__ == "__main__":
    here = Path(__file__).parent
    totals, fails = run_all()
    out = {"totals": totals,
           "fails": {k: v[:20] for k, v in fails.items()},
           "fail_counts": {k: len(v) for k, v in fails.items()}}
    (here / "fuzz_results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out["fail_counts"], indent=2))
    print(f"totals: {totals}")
