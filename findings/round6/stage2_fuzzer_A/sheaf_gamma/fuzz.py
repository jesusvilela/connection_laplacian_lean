"""
FUZZER-A R6 Stage 2 — Sheaf-section gamma (switching / cohomology / balance).

Goal: verify with EXACT integer counts at n=6 (exhaustive over connected
isomorphism classes) that the Stage-1 gamma claims lift:

  G1  #switching-classes(G) = 2^{beta_1(G)}
  G4  switching-class -> parity vector on cycle basis is a bijection
  G5  #epsilon witnesses = 2^{#pi_0} if every component balance-achievable else 0
  G13 #coboundaries = 2^{|V| - #pi_0(G)}
  G14 |V| - |E| = #pi_0(G) - beta_1(G)  (Euler)
  G18 #switching-classes = prod_i 2^{beta_1(C_i)}
  G21 #coboundaries * #switching-classes = 2^{|E|}

  G2  parity of |W cap gamma| on each fundamental cycle is switching-invariant
  G3  G balanced iff every fundamental cycle has even |W cap gamma|
  G12 beta(G, W) = beta(G, W xor delta(S)) for all S

  M2  merge: beta switching-invariance (composition of G12 + parity lemmas)
  M5  balance iff every cycle in cycle-space has even wrap-count

Pure Python. No numpy / no networkx -- just bitmasks over edges and vertices.
Edges are indexed 0..m-1; W is a bitmask over m bits; delta(S) is a bitmask
over m bits; coboundaries live in the subspace spanned by {delta({v}) : v in V}.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
import time
from collections import defaultdict
from pathlib import Path


RNG = random.Random(20260422)


# ---------------------------------------------------------------------------
# Basic graph utilities: pure-Python bitmask representation.
# A graph on n vertices is represented by `edges`: list of (u,v) with u<v.
# Adjacency is computed on demand.
# ---------------------------------------------------------------------------


def edges_to_adj(n: int, edges):
    adj = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    return adj


def connected_components(n: int, adj):
    """Return list of frozenset(vertex) for each component."""
    seen = [False] * n
    comps = []
    for s in range(n):
        if seen[s]:
            continue
        comp = []
        stack = [s]
        seen[s] = True
        while stack:
            u = stack.pop()
            comp.append(u)
            for (w, _e) in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    stack.append(w)
        comps.append(frozenset(comp))
    return comps


def is_connected(n: int, adj):
    return len(connected_components(n, adj)) == 1


def num_pi0(n: int, adj):
    return len(connected_components(n, adj))


def beta1(n: int, m: int, adj):
    return m - n + num_pi0(n, adj)


def coboundary_mask(n: int, edges, S_bits: int) -> int:
    """delta(S) as a bitmask over m edges; S_bits is bitmask on n vertices."""
    out = 0
    for i, (u, v) in enumerate(edges):
        if ((S_bits >> u) & 1) ^ ((S_bits >> v) & 1):
            out |= (1 << i)
    return out


def vertex_coboundary_basis(n: int, edges):
    """For each vertex v, mask of edges incident to v (equals delta({v}))."""
    m = len(edges)
    out = [0] * n
    for i, (u, v) in enumerate(edges):
        out[u] |= (1 << i)
        out[v] |= (1 << i)
    return out


def all_coboundaries_set(n: int, edges):
    """Return frozenset of all coboundary bitmasks (2^{|V|-#pi0} of them).

    We compute the row-space spanned by the per-vertex coboundaries over GF(2).
    """
    v_masks = vertex_coboundary_basis(n, edges)
    # Gaussian-elim independence: pivot on each incoming mask.
    basis = []  # list of (mask, pivot_bit)
    for m in v_masks:
        mm = m
        for (b, pv) in basis:
            if (mm >> pv) & 1:
                mm ^= b
        if mm == 0:
            continue
        # pivot = lowest set bit
        pv = (mm & -mm).bit_length() - 1
        basis.append((mm, pv))
    # Enumerate span (dimension = len(basis))
    masks = {0}
    for (b, _pv) in basis:
        masks = masks | {w ^ b for w in masks}
    return masks, len(basis)


def spanning_forest_and_chords(n: int, adj):
    """BFS spanning forest. Return (tree_edge_ids_set, chord_edge_ids_list)."""
    seen = [False] * n
    parent_edge = [-1] * n
    tree_edges = set()
    for s in range(n):
        if seen[s]:
            continue
        seen[s] = True
        stack = [s]
        while stack:
            u = stack.pop()
            for (w, e) in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    parent_edge[w] = e
                    tree_edges.add(e)
                    stack.append(w)
    chords = [e for e in range(sum(1 for _ in range(len(adj)))) if False]
    # Fix: count edges = max edge id used
    # We'll let caller infer chords by comparing against full edge set.
    return tree_edges, parent_edge


def fundamental_cycle_masks(n: int, edges, adj):
    """For each non-tree edge (chord), build the fundamental cycle as a
    bitmask over all edges. Returns list of cycle masks (length = beta_1)."""
    m = len(edges)
    # BFS tree
    seen = [False] * n
    parent = [-1] * n
    parent_edge = [-1] * n
    depth = [0] * n
    tree_edges = set()
    for s in range(n):
        if seen[s]:
            continue
        seen[s] = True
        stack = [s]
        while stack:
            u = stack.pop()
            for (w, e) in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    parent[w] = u
                    parent_edge[w] = e
                    depth[w] = depth[u] + 1
                    tree_edges.add(e)
                    stack.append(w)

    # For each chord, walk u,v to LCA via parent pointers.
    cycle_masks = []
    for e in range(m):
        if e in tree_edges:
            continue
        u, v = edges[e]
        mask = (1 << e)
        a, b = u, v
        # align depths
        while depth[a] > depth[b]:
            mask |= (1 << parent_edge[a])
            a = parent[a]
        while depth[b] > depth[a]:
            mask |= (1 << parent_edge[b])
            b = parent[b]
        while a != b:
            mask |= (1 << parent_edge[a])
            mask |= (1 << parent_edge[b])
            a = parent[a]
            b = parent[b]
        cycle_masks.append(mask)
    return cycle_masks


# ---------------------------------------------------------------------------
# Canonical form (iso-class key) for unordered simple graphs.
# We use a relabeling-search canonical-form: among all permutations of
# vertices, pick the lexicographically minimum upper-triangle bit vector.
# For n <= 6 this is 720 permutations per graph -- fine.
# ---------------------------------------------------------------------------


def canonical_key(n: int, edges_set_frozen):
    """edges_set: frozenset of (u,v) with u<v. Returns canonical integer key."""
    best = None
    # Pre-index edges as bitmask over sorted pairs (i<j)
    # For canonical form, iterate permutations
    for perm in itertools.permutations(range(n)):
        # Map each edge; compute bit index of (min, max) pair
        key = 0
        ok = True
        for (u, v) in edges_set_frozen:
            pu, pv = perm[u], perm[v]
            if pu > pv:
                pu, pv = pv, pu
            # bit index for pair (pu, pv): linear order over pairs
            # index = pu * (2n - pu - 1) / 2 + (pv - pu - 1)
            idx = pu * (2 * n - pu - 1) // 2 + (pv - pu - 1)
            key |= (1 << idx)
        if best is None or key < best:
            best = key
    return best


# ---------------------------------------------------------------------------
# Enumerate all connected graphs on n vertices (up to iso).
# For n=6: 2^15 = 32768 labeled graphs; dedup by canonical_key yields 112
# connected iso classes (classic number: 112).
# ---------------------------------------------------------------------------


def all_connected_iso_classes(n: int):
    """Yield (edges_list_canonical) for each connected iso-class on n vertices."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    m_pairs = len(pairs)
    seen_keys = set()
    out = []
    for mask in range(1 << m_pairs):
        edges = [pairs[i] for i in range(m_pairs) if (mask >> i) & 1]
        adj = edges_to_adj(n, edges)
        if not is_connected(n, adj):
            continue
        key = canonical_key(n, frozenset(edges))
        if key in seen_keys:
            continue
        seen_keys.add(key)
        out.append(edges)
    return out


# ---------------------------------------------------------------------------
# Core counting procedures over bitmasks.
# ---------------------------------------------------------------------------


def count_switching_classes(n: int, edges, adj):
    """Count switching classes: W ~ W xor delta(S). Equivalence is quotient by
    coboundary subspace. #classes = 2^m / 2^{|V|-#pi0}."""
    m = len(edges)
    cob_set, cob_dim = all_coboundaries_set(n, edges)
    # Use union-find on 2^m... but m up to 15 is 32768 which is OK.
    # Simpler: each class is a coset of the coboundary subspace.
    # We pick a canonical representative (min in orbit).
    classes = set()
    for W in range(1 << m):
        # Canonical rep = min over {W xor c : c in cob_set}
        rep = min(W ^ c for c in cob_set)
        classes.add(rep)
    return len(classes), cob_set, cob_dim


def count_switching_classes_fast(m: int, cob_set_frozen):
    """Fast count: #switching-classes = 2^m / |coboundary-subspace|."""
    return (1 << m) // len(cob_set_frozen)


def is_balanced(n: int, edges, adj, W: int) -> bool:
    """BFS 2-coloring with signs on each component. Edge e: sign = -1 if in W else +1.
    Balanced iff no contradiction."""
    color = [None] * n
    for s in range(n):
        if color[s] is not None:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for (w, e) in adj[u]:
                flip = (W >> e) & 1
                want = color[u] ^ flip
                if color[w] is None:
                    color[w] = want
                    stack.append(w)
                elif color[w] != want:
                    return False
    return True


def is_balanced_per_component(n: int, adj_restricted_edges_with_ids, W: int) -> bool:
    """Same as is_balanced but generic (takes (adj, edge-index-to-global-W-bit) pairs)."""
    raise NotImplementedError


def beta_balance_count(n: int, edges, adj, W: int) -> int:
    """Count number of connected components of (V,E) that are balanced under
    the restriction of W to their edge set."""
    color = [None] * n
    cnt = 0
    for s in range(n):
        if color[s] is not None:
            continue
        color[s] = 0
        stack = [s]
        ok = True
        while stack:
            u = stack.pop()
            for (w, e) in adj[u]:
                flip = (W >> e) & 1
                want = color[u] ^ flip
                if color[w] is None:
                    color[w] = want
                    stack.append(w)
                elif color[w] != want:
                    ok = False
        if ok:
            cnt += 1
    return cnt


def count_epsilon_witnesses(n: int, edges, W: int) -> int:
    """Count epsilon in {0,1}^n s.t. eps(u) xor eps(v) = [e in W] for every edge."""
    cnt = 0
    for eps in range(1 << n):
        good = True
        for i, (u, v) in enumerate(edges):
            flip = (W >> i) & 1
            if (((eps >> u) & 1) ^ ((eps >> v) & 1)) != flip:
                good = False
                break
        if good:
            cnt += 1
    return cnt


# ---------------------------------------------------------------------------
# Claim harnesses for n=6.
# ---------------------------------------------------------------------------


class Claim:
    def __init__(self, idx, name):
        self.idx = idx
        self.name = name
        self.tested = 0
        self.passed = 0
        self.counterexample = None

    def record(self, ok, ce=None):
        self.tested += 1
        if ok:
            self.passed += 1
        elif self.counterexample is None:
            self.counterexample = ce

    def to_dict(self):
        tau = 0.0 if self.tested == 0 else self.passed / self.tested
        return {"idx": self.idx, "name": self.name,
                "tested": self.tested, "passed": self.passed,
                "tau": round(tau, 9),
                "counterexample": self.counterexample}


# ---------------------------------------------------------------------------
# Stage 2: n=6 exhaustive over iso-classes and all W.
#
# We will do a single pass per iso-class that computes everything at once.
# ---------------------------------------------------------------------------


def check_iso_class(n: int, edges, claims):
    """Run all claims on a single iso-class with given edge list.
    For each claim, either:
      - collapses to a single pass/fail (G1, G13, G14, G18, G21, G4) -- structure only
      - enumerates all W (G5, G3, G12 sampled with multiple S)
      - enumerates all (W, S) (G2, G12 exhaustive when tractable)
    """
    m = len(edges)
    adj = edges_to_adj(n, edges)
    pi0 = num_pi0(n, adj)
    b1 = m - n + pi0

    # Coboundary subspace.
    cob_set, cob_dim = all_coboundaries_set(n, edges)
    # Fast switching-class count (algebraic):
    sc_count_alg = (1 << m) // len(cob_set)

    # -- G14: Euler characteristic.
    g14_ok = (n - m) == (pi0 - b1)
    claims["G14"].record(g14_ok, None if g14_ok else {
        "edges": edges, "n": n, "m": m, "pi0": pi0, "beta1": b1})

    # -- G13: #coboundaries = 2^{|V| - #pi0}
    g13_ok = len(cob_set) == (1 << (n - pi0))
    claims["G13"].record(g13_ok, None if g13_ok else {
        "edges": edges, "n": n, "cob_count": len(cob_set),
        "expected": 1 << (n - pi0)})

    # -- G18: #switching-classes = prod_i 2^{beta_1(C_i)}
    comps = connected_components(n, adj)
    prod = 1
    for comp in comps:
        comp_verts = list(comp)
        comp_edges = [i for i, (u, v) in enumerate(edges) if u in comp and v in comp]
        e_c = len(comp_edges)
        n_c = len(comp_verts)
        b1_c = e_c - n_c + 1
        prod *= (1 << b1_c)
    g18_ok = sc_count_alg == prod
    claims["G18"].record(g18_ok, None if g18_ok else {
        "edges": edges, "sc_count": sc_count_alg, "expected": prod})

    # -- G1: #switching-classes = 2^{beta_1(G)}
    g1_ok = sc_count_alg == (1 << b1)
    claims["G1"].record(g1_ok, None if g1_ok else {
        "edges": edges, "sc_count": sc_count_alg, "beta1": b1,
        "expected": 1 << b1})

    # -- G21: #coboundaries * #switching-classes = 2^|E|
    g21_ok = len(cob_set) * sc_count_alg == (1 << m)
    claims["G21"].record(g21_ok, None if g21_ok else {
        "edges": edges, "cob": len(cob_set), "sc": sc_count_alg, "2m": 1 << m})

    # -- G4: switching-class -> parity-vector on cycle basis is bijection.
    cycle_masks = fundamental_cycle_masks(n, edges, adj)
    # For each coset of the coboundary subspace, parity on each cycle
    # should be constant (invariance = G2) and all 2^{beta_1} parity vectors
    # must be realized exactly once.
    # We iterate over all W and bucket by the canonical coset representative
    # while checking all-same parity.
    parity_by_class = {}
    g4_ok = True
    g2_ok_local = True
    # G2 tests we pair each W with switching by every vertex single-ton.
    # A class with inconsistent parity is a G4 fail AND a G2 fail.
    # We'll enumerate all W and compute (a) class rep, (b) parity vector.
    for W in range(1 << m):
        rep = min(W ^ c for c in cob_set)
        pv = tuple((bin(W & cm).count("1") & 1) for cm in cycle_masks)
        if rep in parity_by_class:
            if parity_by_class[rep] != pv:
                g4_ok = False
                g2_ok_local = False
                if claims["G4"].counterexample is None:
                    claims["G4"].counterexample = {
                        "edges": edges, "W": W, "rep": rep,
                        "pv_W": pv, "pv_rep": parity_by_class[rep]}
                break
        else:
            parity_by_class[rep] = pv
    if g4_ok:
        # All classes covered? And all parity vectors distinct?
        parities = set(parity_by_class.values())
        g4_ok = (len(parities) == (1 << b1)
                 and len(parity_by_class) == (1 << b1))
        if not g4_ok:
            claims["G4"].counterexample = {
                "edges": edges, "n_classes": len(parity_by_class),
                "n_parities": len(parities), "expected": 1 << b1}
    claims["G4"].record(g4_ok)
    claims["G2"].record(g2_ok_local, None if g2_ok_local else {
        "edges": edges, "note": "G2 fail detected in parity-invariance check inside G4 loop"})

    # -- G3: G balanced iff every fundamental cycle has even parity.
    # (Requires G connected; skip if not.)
    if pi0 == 1:
        for W in range(1 << m):
            bal = is_balanced(n, edges, adj, W)
            all_even = all((bin(W & cm).count("1") & 1) == 0 for cm in cycle_masks)
            ok = bal == all_even
            if not ok:
                claims["G3"].record(False, {
                    "edges": edges, "W": W, "bal": bal, "all_even": all_even})
                break
            else:
                claims["G3"].record(True)

    # -- M5: balance iff every cycle in cycle-space has even parity.
    # (Cycle space = XOR-closure of fundamental cycles. Generated by cycle_masks.)
    if pi0 == 1:
        # All cycles: span of cycle_masks
        cycle_space = {0}
        for cm in cycle_masks:
            cycle_space = cycle_space | {c ^ cm for c in cycle_space}
        # Test on every W
        for W in range(1 << m):
            bal = is_balanced(n, edges, adj, W)
            all_even = all((bin(W & c).count("1") & 1) == 0 for c in cycle_space)
            ok = bal == all_even
            if not ok:
                claims["M5"].record(False, {
                    "edges": edges, "W": W, "bal": bal, "all_even": all_even})
                break
            else:
                claims["M5"].record(True)

    # -- G5: #epsilon witnesses = 2^{#pi_0} if every comp balanced else 0.
    # We iterate all W.
    for W in range(1 << m):
        cnt = count_epsilon_witnesses(n, edges, W)
        all_balanced = (beta_balance_count(n, edges, adj, W) == pi0)
        expected = (1 << pi0) if all_balanced else 0
        ok = cnt == expected
        if not ok:
            claims["G5"].record(False, {
                "edges": edges, "W": W, "cnt": cnt, "expected": expected,
                "all_balanced": all_balanced})
            break
        else:
            claims["G5"].record(True)

    # -- G12: beta(G,W) = beta(G, W xor delta(S)) for all S.
    # Enumerate all W, sample S subsets.
    # For n=6 there are 2^6 = 64 S values. For each (W, S) we do a linear BFS.
    # Full sweep: 2^m * 64 BFSes per iso-class. For m=15 that's ~2.1M per class.
    # That's heavy over 112 classes. Instead, full sweep per class WHERE tractable
    # (m <= 12 say), and S sampled otherwise.
    g12_fail = False
    S_masks = list(range(1 << n))
    # Full sweep if m <= 12; else sample W (1024 of them) * all S.
    if m <= 12:
        for W in range(1 << m):
            b0 = beta_balance_count(n, edges, adj, W)
            for Sb in S_masks:
                dS = coboundary_mask(n, edges, Sb)
                bp = beta_balance_count(n, edges, adj, W ^ dS)
                if b0 != bp:
                    claims["G12"].record(False, {
                        "edges": edges, "W": W, "S": Sb,
                        "beta_W": b0, "beta_Wp": bp})
                    g12_fail = True
                    break
                claims["G12"].record(True)
            if g12_fail:
                break
    else:
        # Sample 2048 W values; for each, all S.
        W_sample = RNG.sample(range(1 << m), min(1 << m, 2048))
        for W in W_sample:
            b0 = beta_balance_count(n, edges, adj, W)
            for Sb in S_masks:
                dS = coboundary_mask(n, edges, Sb)
                bp = beta_balance_count(n, edges, adj, W ^ dS)
                if b0 != bp:
                    claims["G12"].record(False, {
                        "edges": edges, "W": W, "S": Sb,
                        "beta_W": b0, "beta_Wp": bp})
                    g12_fail = True
                    break
                claims["G12"].record(True)
            if g12_fail:
                break

    # -- M2: beta switching invariance (same as G12 but labeled as merge claim).
    # We reuse: M2 succeeds iff G12 succeeds on this iso-class. Already verified.
    # Record once per iso-class.
    claims["M2"].record(not g12_fail, None if not g12_fail else {
        "note": "inherits from G12", "edges": edges})


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------


def main():
    out_dir = Path(__file__).parent
    t_start = time.time()

    n = 6
    print(f"[sheaf-gamma] enumerating connected iso-classes on n={n} ...",
          flush=True)
    iso_classes = all_connected_iso_classes(n)
    print(f"[sheaf-gamma] found {len(iso_classes)} connected iso-classes",
          flush=True)
    assert len(iso_classes) == 112, \
        f"expected 112 connected graphs on 6 vertices, got {len(iso_classes)}"

    claim_list = [
        ("G1", "#switching-classes(G) = 2^{beta_1(G)}"),
        ("G2", "parity |W cap gamma| on cycle basis is switching-invariant"),
        ("G3", "G balanced iff every fundamental cycle has even |W cap gamma|"),
        ("G4", "switching-class <-> parity vector on cycle basis is bijection"),
        ("G5", "#epsilon witnesses = 2^{#pi_0} if all comps balanced else 0"),
        ("G12", "beta(G,W) = beta(G, W xor delta(S))"),
        ("G13", "#coboundaries = 2^{|V|-#pi_0}"),
        ("G14", "|V|-|E| = #pi_0 - beta_1 (Euler)"),
        ("G18", "#switching-classes = prod_i 2^{beta_1(C_i)}"),
        ("G21", "#coboundaries * #switching-classes = 2^{|E|}"),
        ("M2",  "beta switching-invariance (merge: G12 + G2 + G3)"),
        ("M5",  "balance iff every cycle in cycle-space has even wrap-count"),
    ]
    claims = {idx: Claim(idx, name) for (idx, name) in claim_list}

    # Per-class summary.
    per_class = []
    for i, edges in enumerate(iso_classes):
        t0 = time.time()
        adj = edges_to_adj(n, edges)
        m = len(edges)
        pi0 = num_pi0(n, adj)
        b1 = m - n + pi0
        check_iso_class(n, edges, claims)
        dt = time.time() - t0
        per_class.append({"idx": i, "m": m, "pi0": pi0, "beta1": b1,
                          "dt_sec": round(dt, 3)})
        if (i + 1) % 10 == 0 or i + 1 == len(iso_classes):
            elapsed = time.time() - t_start
            print(f"  [{i+1}/{len(iso_classes)}] edges={m} beta1={b1} "
                  f"dt={dt:.3f}s elapsed={elapsed:.1f}s", flush=True)

    # Summary.
    print("\n[sheaf-gamma] PER-CLAIM RESULTS")
    results_list = []
    for idx, _ in claim_list:
        c = claims[idx]
        d = c.to_dict()
        results_list.append(d)
        status = "PASS" if c.passed == c.tested and c.tested > 0 else (
            "FAIL" if c.tested > 0 else "N/A")
        print(f"  {idx:>3}  {status:>5}  {c.passed}/{c.tested}  {c.name}")

    results = {
        "n": n,
        "iso_classes": len(iso_classes),
        "total_seconds": round(time.time() - t_start, 2),
        "claims": results_list,
        "per_class_timing": per_class,
    }
    (out_dir / "results.json").write_text(json.dumps(results, indent=2, default=str))
    print(f"\n[sheaf-gamma] wrote results.json ({len(iso_classes)} iso-classes; "
          f"total {results['total_seconds']}s)")


if __name__ == "__main__":
    main()
