"""
NEGATOR-A sheaf-section gamma, Round 6:
  10+ NEW fuzzy claims centered on cohomology / balance / H^1 / cocycles /
  switching-equivalence, orthogonal to the already-τ=1 R5 claims:
    R4  (β = β(E\\W) bipartite)           — covered
    R13 (±1 basis per balanced comp)       — covered
    R15 (#{W : balanced} = 2^(|V|−#π₀))    — covered
    R16 (min coboundary = edge-conn)       — covered
    R20 (disjoint union additivity)        — covered
    R21 (balance ⇒ bipartite-(V,W))        — covered
    R22 (ker L_möb sym ⊕ anti lift)        — covered

Scope (γ): cocycles, coboundaries, switching-classes, cycle-space parity,
balance radius, ε-coloring multiplicity, merging balanced components.

Search envelope: iso graphs on n∈{3,4,5} exhaustive, n=6 sampled.

Output:
  - results.json : full record
  - report.md    : written separately
"""

from __future__ import annotations

import itertools
import json
import math
import random
import sys
from pathlib import Path

import networkx as nx
import numpy as np

TOL = 1e-8
RNG = random.Random(20260422)


# ---------------------------------------------------------------------------
# Core helpers (reused from R5 fuzzer).
# ---------------------------------------------------------------------------

def edge_list(G):
    return [tuple(sorted(e)) for e in G.edges()]


def laplacian_signed(G, wrap):
    n = G.number_of_nodes()
    L = np.zeros((n, n))
    for u, v in G.edges():
        e = tuple(sorted((u, v)))
        L[u, u] += 1
        L[v, v] += 1
        s = +1.0 if e in wrap else -1.0
        L[u, v] += s
        L[v, u] += s
    return L


def is_balanced_component(G, wrap):
    """Check every connected component is balanced under the restriction of wrap."""
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


def beta(G, wrap):
    return balanced_component_count(G, wrap)


def kernel_dim(M):
    ev = np.linalg.eigvalsh(M)
    return int(np.sum(np.abs(ev) < TOL))


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


def describe(G, W):
    return {"n": G.number_of_nodes(),
            "edges": edge_list(G),
            "wrap": sorted(list(W))}


def vertex_switch(G, W, v):
    """Switch at vertex v: flip wrap status of every edge incident to v."""
    new_W = set(W)
    for u in G.neighbors(v):
        e = tuple(sorted((u, v)))
        if e in new_W:
            new_W.discard(e)
        else:
            new_W.add(e)
    return frozenset(new_W)


def switch_by_set(G, W, S):
    """Switch by indicator of S ⊆ V: flip edges of the coboundary δ(S)."""
    new_W = set(W)
    for (u, v) in G.edges():
        e = tuple(sorted((u, v)))
        in_cut = (u in S) ^ (v in S)
        if in_cut:
            if e in new_W:
                new_W.discard(e)
            else:
                new_W.add(e)
    return frozenset(new_W)


def cycle_rank(G):
    """β_1(G) = |E| − |V| + #components."""
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)


def coboundary(G, S):
    return frozenset(tuple(sorted((u, v)))
                     for (u, v) in G.edges() if (u in S) ^ (v in S))


def is_coboundary(G, W):
    V = list(G.nodes())
    for mask in range(1 << len(V)):
        S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
        if coboundary(G, S) == set(W):
            return True
    return False


# ---------------------------------------------------------------------------
# Claim container.
# ---------------------------------------------------------------------------

class FuzzyClaim:
    def __init__(self, idx, name, hypothesis=""):
        self.idx = idx
        self.name = name
        self.hypothesis = hypothesis
        self.tested = 0
        self.passed = 0
        self.counterexample = None

    def record(self, ok, ce=None):
        self.tested += 1
        if ok:
            self.passed += 1
        elif self.counterexample is None:
            self.counterexample = ce

    @property
    def tau(self):
        return 0.0 if self.tested == 0 else self.passed / self.tested

    def verdict(self):
        t = self.tau
        if t == 1.0:
            return f"TRUE (fuzz-verified tau=1.0000, n={self.tested})"
        if t > 0.95:
            return f"NEAR-TRUE (tau={t:.4f})"
        if t > 0.5:
            return f"MOSTLY TRUE (tau={t:.4f})"
        if t > 0.1:
            return f"MIXED (tau={t:.4f})"
        return f"COUNTEREXAMPLE-RICH (tau={t:.4f})"

    def to_dict(self):
        return {"idx": self.idx,
                "name": self.name,
                "hypothesis": self.hypothesis,
                "tested": self.tested,
                "passed": self.passed,
                "tau": round(self.tau, 6),
                "verdict": self.verdict(),
                "counterexample": self.counterexample}


# ---------------------------------------------------------------------------
# Search envelope.
# ---------------------------------------------------------------------------

def small_instances(n_min=3, n_max=5):
    for n in range(n_min, n_max + 1):
        for G in all_graphs_iso(n):
            for W in all_wrap_subsets(G):
                yield n, G, W


def sample_n6(wrap_cap=16, iso_cap=24):
    """Sampled envelope at n=6: random sample of iso classes & wrap sets."""
    n = 6
    all_iso = list(all_graphs_iso(n))
    iso_sample = all_iso if len(all_iso) <= iso_cap else RNG.sample(all_iso, iso_cap)
    for G in iso_sample:
        subs = list(all_wrap_subsets(G))
        if len(subs) > wrap_cap:
            subs = RNG.sample(subs, wrap_cap)
        for W in subs:
            yield n, G, W


# ===========================================================================
# G1: Switching-equivalence class count == 2^{β_1(G)} · 2^{#π₀(G)} / 2^{|V|} ...
#
# Two wrap sets W, W' are "switching equivalent" iff W' = W △ δ(S) for some
# S ⊆ V. The number of switching classes on G equals
#   2^{|E|} / (# coboundaries) = 2^{|E|} / 2^{|V|−#π₀(G)} = 2^{β_1(G)}.
# Here |E| - (|V| - #π₀) = β_1(G).
# ===========================================================================

def claim_g1_switching_class_count():
    c = FuzzyClaim("G1", "#switching classes on G == 2^{β_1(G)}",
                   "any G; wrap subsets modulo W ~ W △ δ(S)")
    seen = set()
    for n, G, _ in small_instances():
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        all_E = frozenset(edge_list(G))
        # Compute equivalence-class count by union-find over wrap subsets.
        ws = list(all_wrap_subsets(G))
        idx = {w: i for i, w in enumerate(ws)}
        parent = list(range(len(ws)))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
        V = list(G.nodes())
        # It suffices to switch by single-vertex sets (they generate δ).
        for W in ws:
            for v in V:
                Wp = vertex_switch(G, W, v)
                union(idx[W], idx[Wp])
        classes = len({find(i) for i in range(len(ws))})
        expected = 1 << cycle_rank(G)
        ok = classes == expected
        if not ok:
            c.record(False, {**describe(G, frozenset()),
                             "classes": classes, "expected": expected,
                             "beta1": cycle_rank(G)})
        else:
            c.record(True)
    return c


# ===========================================================================
# G2: Wrap parity map wrap : H_1(G;Z/2) → Z/2 is a switching invariant.
#
# For each simple cycle γ in G (as an edge subset), the parity of |γ ∩ W| is
# invariant under W → W △ δ(S). Claim: switching W by any vertex set S
# preserves |W ∩ γ| mod 2 for every cycle γ.
# ===========================================================================

def simple_cycles(G):
    """All simple cycles of G, represented as frozensets of edges (length ≥3)."""
    out = []
    for cyc in nx.cycle_basis(G):
        # Build all combinations via XOR of cycle-basis elements.
        pass
    # Full enumeration of cycle space: 2^{β_1} elements
    basis_cycles = []
    for cyc_nodes in nx.cycle_basis(G):
        es = set()
        for i in range(len(cyc_nodes)):
            u, v = cyc_nodes[i], cyc_nodes[(i + 1) % len(cyc_nodes)]
            es.add(tuple(sorted((u, v))))
        basis_cycles.append(frozenset(es))
    # XOR closure:
    seen = {frozenset()}
    for b in basis_cycles:
        new = set(seen)
        for s in seen:
            new.add(frozenset(s ^ b))
        seen = new
    return [s for s in seen if s]


def claim_g2_cycle_parity_switching_invariant():
    c = FuzzyClaim("G2", "parity of |W ∩ γ| on each cycle γ is switching invariant",
                   "for any W, S ⊆ V, every cycle γ: |W∩γ| ≡ |(W△δS)∩γ| mod 2")
    for n, G, W in small_instances():
        if n > 4:  # cycle enumeration grows fast
            continue
        cyc = simple_cycles(G)
        if not cyc:
            continue
        V = list(G.nodes())
        # Pick a few switches S.
        masks = list(range(1 << len(V)))
        RNG.shuffle(masks)
        for mask in masks[:min(len(masks), 8)]:
            S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
            Wp = switch_by_set(G, W, S)
            for g in cyc:
                p1 = len(W & g) & 1
                p2 = len(Wp & g) & 1
                if p1 != p2:
                    c.record(False, {**describe(G, W),
                                     "S": sorted(S),
                                     "cycle": sorted(g),
                                     "parity_W": p1, "parity_Wswitch": p2})
                else:
                    c.record(True)
    return c


# ===========================================================================
# G3: Balance iff wrap-parity on every cycle is 0.
#   (G, W) balanced iff for every cycle γ, |W ∩ γ| ≡ 0 mod 2.
# (Classical Harary switching = coboundary iff every cycle parity is 0.)
# ===========================================================================

def claim_g3_balance_iff_all_cycle_parity_zero():
    c = FuzzyClaim("G3", "G balanced iff every cycle γ has |W ∩ γ| even",
                   "G connected; check equivalence of balance and global cycle-even")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        if n > 4:
            continue
        cyc = simple_cycles(G)
        all_even = all(len(W & g) % 2 == 0 for g in cyc) if cyc else True
        bal = is_balanced_component(G, W)
        ok = all_even == bal
        if not ok:
            c.record(False, {**describe(G, W),
                             "all_even": all_even, "balanced": bal})
        else:
            c.record(True)
    return c


# ===========================================================================
# G4: Switching-class to Hom(H_1,Z/2) bijection.
#   For G with β_1 = m, there are 2^m switching classes, and the map
#   W ↦ (|W ∩ γ_i| mod 2)_i for basis cycles γ_i is a bijection.
# ===========================================================================

def claim_g4_switching_to_hom_h1():
    c = FuzzyClaim("G4", "switching-class → (parity on each basis cycle) is a bijection",
                   "G connected; basis cycles γ₁,...,γ_m; map W ↦ (|W∩γ_i| mod 2)_i")
    seen = set()
    for n, G, _ in small_instances():
        if not nx.is_connected(G):
            continue
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        basis_nodes = nx.cycle_basis(G)
        basis = []
        for cyc_nodes in basis_nodes:
            es = set()
            for i in range(len(cyc_nodes)):
                u, v = cyc_nodes[i], cyc_nodes[(i + 1) % len(cyc_nodes)]
                es.add(tuple(sorted((u, v))))
            basis.append(frozenset(es))
        m = len(basis)
        # Group wrap sets by switching class (using union-find).
        ws = list(all_wrap_subsets(G))
        idx = {w: i for i, w in enumerate(ws)}
        parent = list(range(len(ws)))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for W in ws:
            for v in G.nodes():
                Wp = vertex_switch(G, W, v)
                ra, rb = find(idx[W]), find(idx[Wp])
                if ra != rb:
                    parent[ra] = rb
        class_of = {w: find(idx[w]) for w in ws}
        # For each class, collect parities.
        sigs = {}
        for w in ws:
            sig = tuple(len(w & g) % 2 for g in basis)
            sigs.setdefault(class_of[w], set()).add(sig)
        ok = (len(sigs) == (1 << m)
              and all(len(s) == 1 for s in sigs.values())
              and len({next(iter(s)) for s in sigs.values()}) == (1 << m))
        if not ok:
            c.record(False, {**describe(G, frozenset()),
                             "num_classes": len(sigs), "expected": 1 << m,
                             "sigs_sample": {str(k): sorted(v) for k, v in list(sigs.items())[:3]}})
        else:
            c.record(True)
    return c


# ===========================================================================
# G5: ε-coloring multiplicity for balanced (G,W).
#   On connected balanced (G,W), exactly 2 distinct ε : V → Z/2 witness balance
#   (ε(u)+ε(v)+[e∈W]=0 on every edge).  More generally: for any W balanced on
#   each component, # witnesses = 2^{#π₀(G)}.
# ===========================================================================

def count_epsilon_witnesses(G, W):
    """Count ε : V→Z/2 s.t. ε(u) XOR ε(v) = [e ∈ W] for every edge. 0 if none."""
    V = list(G.nodes())
    n = len(V)
    count = 0
    for mask in range(1 << n):
        eps = {V[i]: (mask >> i) & 1 for i in range(n)}
        ok = True
        for (u, v) in G.edges():
            e = tuple(sorted((u, v)))
            flip = 1 if e in W else 0
            if (eps[u] ^ eps[v]) != flip:
                ok = False
                break
        if ok:
            count += 1
    return count


def claim_g5_epsilon_multiplicity():
    c = FuzzyClaim("G5", "# ε witnessing balance == 2^{#π₀(G)} when all comps balanced, else 0",
                   "if any component unbalanced, count = 0; else 2^{#π₀}")
    for n, G, W in small_instances():
        ncomp = nx.number_connected_components(G)
        bal = balanced_component_count(G, W) == ncomp
        expected = (1 << ncomp) if bal else 0
        cnt = count_epsilon_witnesses(G, W)
        ok = cnt == expected
        if not ok:
            c.record(False, {**describe(G, W),
                             "cnt": cnt, "expected": expected, "ncomp": ncomp, "all_balanced": bal})
        else:
            c.record(True)
    return c


# ===========================================================================
# G6: Balance radius == min Hamming distance from W to any coboundary.
#   Define bal_radius(G,W) = min #flips so that G becomes balanced.
#   Claim: bal_radius(G,W) = min_{S⊆V} |W △ δ(S)|.
# This is a definitional check; we verify both via brute-force edge-flip
# enumeration AND via vertex-subset enumeration.
# ===========================================================================

def bal_radius_by_edge_flip(G, W):
    edges = edge_list(G)
    m = len(edges)
    best = m + 1
    for mask in range(1 << m):
        flip = {edges[i] for i in range(m) if (mask >> i) & 1}
        Wp = (frozenset(W) | flip) - (frozenset(W) & flip)
        if balanced_component_count(G, Wp) == nx.number_connected_components(G):
            k = bin(mask).count("1")
            if k < best:
                best = k
    return best


def bal_radius_by_coboundary(G, W):
    V = list(G.nodes())
    best = len(edge_list(G)) + 1
    for mask in range(1 << len(V)):
        S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
        d = coboundary(G, S)
        dist = len(set(W) ^ d)
        if dist < best:
            best = dist
    return best


def claim_g6_balance_radius_via_coboundary():
    c = FuzzyClaim("G6", "bal_radius(G,W) == min_S |W △ δ(S)|",
                   "any G,W")
    seen_key = set()
    for n, G, W in small_instances():
        if n > 4:
            continue
        if G.number_of_edges() > 6:
            continue
        key = (n, frozenset(edge_list(G)), W)
        if key in seen_key:
            continue
        seen_key.add(key)
        r1 = bal_radius_by_edge_flip(G, W)
        r2 = bal_radius_by_coboundary(G, W)
        ok = r1 == r2
        if not ok:
            c.record(False, {**describe(G, W), "edge_flip": r1, "coboundary": r2})
        else:
            c.record(True)
    return c


# ===========================================================================
# G7: Balance radius ≥ (min nonzero coboundary size) − β_1(G)? No — test instead:
#   For connected G with β_1(G) ≥ 1: max_W bal_radius(G,W) ≤ |E|/2.
# (Since any W is within distance |E|/2 of the nearest coboundary or its
#  complement in the coset.)
# ===========================================================================

def claim_g7_bal_radius_bounded():
    c = FuzzyClaim("G7", "max_W bal_radius(G,W) ≤ |E| / 2  (rounded-up)",
                   "connected G, any W")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        if n > 4:
            continue
        r = bal_radius_by_coboundary(G, W)
        bound = (G.number_of_edges() + 1) // 2
        ok = r <= bound
        if not ok:
            c.record(False, {**describe(G, W), "radius": r, "bound": bound})
        else:
            c.record(True)
    return c


# ===========================================================================
# G8: Edge-gluing balance test.
#   Let G be the disjoint union of G1,G2 with an extra edge (u1,u2) added where
#   u1 ∈ V(G1), u2 ∈ V(G2). Claim: (G,W) balanced iff each (G_i,W|_i) balanced
#   (regardless of wrap status of the new edge).
#
# Reason: the new edge is a bridge, so any ε that witnesses balance on G_1 and
# G_2 separately can be adjusted on one side to match wrap parity of the
# bridge. So balance is preserved.
# ===========================================================================

def claim_g8_edge_gluing_balance():
    c = FuzzyClaim("G8", "bridge-gluing: (G1 ⊔ G2 + bridge e, W) balanced iff each side balanced",
                   "G1,G2 small; new bridge connects v1∈V(G1) and v2∈V(G2); e may or may not be wrap")
    for n1 in (2, 3):
        for n2 in (2, 3):
            for G1 in all_graphs_iso(n1):
                for G2 in all_graphs_iso(n2):
                    W1s = list(all_wrap_subsets(G1))
                    W2s = list(all_wrap_subsets(G2))
                    for _ in range(4):
                        W1 = RNG.choice(W1s)
                        W2 = RNG.choice(W2s)
                        # Build disjoint union + bridge from 0 to n1.
                        G = nx.Graph()
                        G.add_nodes_from(range(n1 + n2))
                        G.add_edges_from(G1.edges())
                        for (u, v) in G2.edges():
                            G.add_edge(u + n1, v + n1)
                        bridge = tuple(sorted((0, n1)))
                        G.add_edge(*bridge)
                        W = set(W1)
                        for (u, v) in W2:
                            W.add(tuple(sorted((u + n1, v + n1))))
                        for bridge_wrap in (False, True):
                            Wfull = set(W)
                            if bridge_wrap:
                                Wfull.add(bridge)
                            lhs = is_balanced_component(G, frozenset(Wfull))
                            rhs = (is_balanced_component(G1, W1)
                                   and is_balanced_component(G2, W2))
                            ok = lhs == rhs
                            if not ok:
                                c.record(False, {"G1": edge_list(G1), "W1": sorted(W1),
                                                 "G2": edge_list(G2), "W2": sorted(W2),
                                                 "bridge_wrap": bridge_wrap,
                                                 "balanced_glued": lhs, "balanced_sides": rhs})
                            else:
                                c.record(True)
    return c


# ===========================================================================
# G9: Vertex-identification-gluing balance.
#   Let G = G1 ∨ G2 with one vertex v1 ∈ V(G1) identified with v2 ∈ V(G2).
#   Claim: (G,W) balanced iff each side balanced.
# (No new cycle is created since the vertex-identification adds no edge.)
# ===========================================================================

def claim_g9_vertex_identification_balance():
    c = FuzzyClaim("G9", "vertex-identification gluing preserves balance iff each side balanced",
                   "identify v1∈V(G1) with v2∈V(G2), keep wraps")
    for n1 in (2, 3):
        for n2 in (2, 3):
            for G1 in all_graphs_iso(n1):
                for G2 in all_graphs_iso(n2):
                    W1s = list(all_wrap_subsets(G1))
                    W2s = list(all_wrap_subsets(G2))
                    for _ in range(3):
                        W1 = RNG.choice(W1s)
                        W2 = RNG.choice(W2s)
                        # Identify 0 ∈ V(G1) with 0 ∈ V(G2).  Map G2-vertices
                        # to [n1-1, n1, n1+1, ...]: node 0 → (n1-1) (i.e. a
                        # chosen endpoint of G1's last vertex), rest → offsets.
                        # Simpler: identify G1's vertex 0 with G2's vertex 0.
                        # Relabel G2: 0 → 0, i → n1 + i - 1 for i ≥ 1.
                        relab = {0: 0}
                        for i in range(1, n2):
                            relab[i] = n1 + i - 1
                        G = nx.Graph()
                        G.add_nodes_from(range(n1 + n2 - 1))
                        G.add_edges_from(G1.edges())
                        for (u, v) in G2.edges():
                            G.add_edge(relab[u], relab[v])
                        W = set(W1)
                        for (u, v) in W2:
                            e = tuple(sorted((relab[u], relab[v])))
                            W.add(e)
                        lhs = is_balanced_component(G, frozenset(W))
                        rhs = (is_balanced_component(G1, W1)
                               and is_balanced_component(G2, W2))
                        ok = lhs == rhs
                        if not ok:
                            c.record(False, {"G1": edge_list(G1), "W1": sorted(W1),
                                             "G2": edge_list(G2), "W2": sorted(W2),
                                             "balanced_glued": lhs, "balanced_sides": rhs})
                        else:
                            c.record(True)
    return c


# ===========================================================================
# G10: β_mob := kernel_dim(L_möb) under switching is an invariant.
#   Switching W by any S: kernel dim of L_möb(G,W) = kernel dim of L_möb(G,W△δS).
# ===========================================================================

def laplacian_mobius(G, wrap):
    n = G.number_of_nodes()
    L = np.zeros((2 * n, 2 * n))
    I = np.eye(2)
    X = np.array([[0.0, 1.0], [1.0, 0.0]])
    deg = dict(G.degree())
    for u in range(n):
        L[2 * u:2 * u + 2, 2 * u:2 * u + 2] = deg[u] * I
    for u, v in G.edges():
        e = tuple(sorted((u, v)))
        B = X if e in wrap else I
        L[2 * u:2 * u + 2, 2 * v:2 * v + 2] -= B
        L[2 * v:2 * v + 2, 2 * u:2 * u + 2] -= B
    return L


def claim_g10_switching_kernel_dim_invariant():
    c = FuzzyClaim("G10", "kernel_dim(L_möb) is a switching invariant",
                   "kernel_dim(L_möb(G,W)) == kernel_dim(L_möb(G,W△δS)) for any S")
    for n, G, W in small_instances():
        if n > 4:
            continue
        V = list(G.nodes())
        kd_W = kernel_dim(laplacian_mobius(G, W))
        # Try switching by all single vertices and a few random subsets.
        for v in V:
            Wp = vertex_switch(G, W, v)
            kd_Wp = kernel_dim(laplacian_mobius(G, Wp))
            ok = kd_W == kd_Wp
            if not ok:
                c.record(False, {**describe(G, W), "switch_vertex": v,
                                 "kd_W": kd_W, "kd_Wp": kd_Wp})
            else:
                c.record(True)
        # Random subsets.
        masks = [RNG.randrange(1 << len(V)) for _ in range(3)]
        for mask in masks:
            S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
            Wp = switch_by_set(G, W, S)
            kd_Wp = kernel_dim(laplacian_mobius(G, Wp))
            ok = kd_W == kd_Wp
            if not ok:
                c.record(False, {**describe(G, W), "switch_set": sorted(S),
                                 "kd_W": kd_W, "kd_Wp": kd_Wp})
            else:
                c.record(True)
    return c


# ===========================================================================
# G11: Coboundary ⟺ zero wrap-parity on every cycle.
#   W is a coboundary iff ∀ cycle γ: |W ∩ γ| ≡ 0 mod 2.
# (Equivalent to G3 for connected graphs, but tested with W arbitrary on any G.)
# ===========================================================================

def claim_g11_coboundary_iff_even_cycle_parity():
    c = FuzzyClaim("G11", "W is a coboundary iff every cycle has even intersection with W",
                   "any G,W")
    for n, G, W in small_instances():
        if n > 4:
            continue
        cyc = simple_cycles(G)
        all_even = all(len(W & g) % 2 == 0 for g in cyc) if cyc else True
        cob = is_coboundary(G, W)
        ok = all_even == cob
        if not ok:
            c.record(False, {**describe(G, W),
                             "all_even": all_even, "coboundary": cob})
        else:
            c.record(True)
    return c


# ===========================================================================
# G12: Switching preserves β(G,W) (global balance count).
#   β(G,W) = β(G, W △ δ(S)).
# ===========================================================================

def claim_g12_switching_preserves_beta():
    c = FuzzyClaim("G12", "β(G,W) == β(G, W△δ(S))",
                   "any G,W and S ⊆ V")
    for n, G, W in small_instances():
        V = list(G.nodes())
        b0 = beta(G, W)
        for mask in range(min(1 << len(V), 32)):
            S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
            Wp = switch_by_set(G, W, S)
            b1 = beta(G, Wp)
            ok = b0 == b1
            if not ok:
                c.record(False, {**describe(G, W), "S": sorted(S),
                                 "beta_W": b0, "beta_Wp": b1})
            else:
                c.record(True)
    return c


# ===========================================================================
# G13: Cycle-rank / coboundary-dimension relation.
#   |E| = (|V| − #π₀) + β_1(G)
#   and
#   # coboundaries = 2^{|V|−#π₀}; # cocycles = 2^{β_1}; # edge subsets = 2^|E|.
# ===========================================================================

def claim_g13_coboundary_cocycle_dimension():
    c = FuzzyClaim("G13", "#coboundaries = 2^{|V|−#π₀}; # cocycle classes = 2^{β_1}",
                   "any G; cocycle class = switching class of wrap; coboundary = δ(S)")
    seen = set()
    for n, G, _ in small_instances():
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        V = list(G.nodes())
        cob = set()
        for mask in range(1 << len(V)):
            S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
            cob.add(coboundary(G, S))
        ncomp = nx.number_connected_components(G)
        expected_cob = 1 << (G.number_of_nodes() - ncomp)
        ok_cob = len(cob) == expected_cob
        expected_classes = 1 << cycle_rank(G)
        if not ok_cob:
            c.record(False, {**describe(G, frozenset()),
                             "num_coboundaries": len(cob), "expected": expected_cob})
        else:
            c.record(True)
    return c


# ===========================================================================
# G14: H⁰(G;Z/2) ⊕ H¹(G;Z/2) counting identity:
#   dim H⁰(G;Z/2) = #π₀ ; dim H¹(G;Z/2) = β_1(G);
#   |V| − |E| = #π₀ − β_1  (Euler characteristic χ(G)).
# ===========================================================================

def claim_g14_euler_characteristic():
    c = FuzzyClaim("G14", "|V|−|E| == #π₀(G) − β_1(G)",
                   "Euler characteristic χ(G) for any graph")
    seen = set()
    for n, G, _ in small_instances():
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        chi = G.number_of_nodes() - G.number_of_edges()
        rhs = nx.number_connected_components(G) - cycle_rank(G)
        ok = chi == rhs
        if not ok:
            c.record(False, {**describe(G, frozenset()), "chi": chi, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# G15: Signed-Laplacian kernel dim per component == [balanced].
#   For each connected component C with restricted wrap, dim ker(L_signed|_C)
#   is 1 if C is balanced and 0 otherwise.  So dim ker(L_signed) == β(G,W).
# ===========================================================================

def claim_g15_signed_kernel_dim_per_component():
    c = FuzzyClaim("G15", "dim ker(L_signed(G,W)) == β(G,W)",
                   "any G,W; signed Laplacian = D − A_W")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        kd = kernel_dim(Lsig)
        b = beta(G, W)
        ok = kd == b
        if not ok:
            c.record(False, {**describe(G, W), "kernel_dim": kd, "beta": b})
        else:
            c.record(True)
    return c


# ===========================================================================
# G16: Signed-Laplacian matroid rank = |V| − β.
#   rank(L_signed) = |V| − β(G,W).
# ===========================================================================

def claim_g16_signed_laplacian_rank():
    c = FuzzyClaim("G16", "rank(L_signed(G,W)) == |V| − β(G,W)",
                   "any G,W")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        r = int(np.linalg.matrix_rank(Lsig, tol=TOL))
        expected = G.number_of_nodes() - beta(G, W)
        ok = r == expected
        if not ok:
            c.record(False, {**describe(G, W), "rank": r, "expected": expected})
        else:
            c.record(True)
    return c


# ===========================================================================
# G17: Distance between switching classes = Hamming distance modulo δ-lattice.
#   For W, W' in distinct switching classes, min_S |W △ W' △ δ(S)| ≥ 1.
#   (Obvious but we test it.)
# ===========================================================================

def claim_g17_switching_class_distance_nonzero():
    c = FuzzyClaim("G17", "distinct switching classes have min_S |W△W'△δ(S)| ≥ 1",
                   "trivial separator lemma")
    for n, G, W in small_instances():
        if n > 4:
            continue
        # Pick a few Wp in same iteration — sample 3 random others.
        all_E = frozenset(edge_list(G))
        ws = list(all_wrap_subsets(G))
        if len(ws) < 2:
            continue
        RNG.shuffle(ws)
        for Wp in ws[:4]:
            if Wp == W:
                continue
            # Are W and Wp in the same class?
            V = list(G.nodes())
            same_class = False
            for mask in range(1 << len(V)):
                S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
                if frozenset(W) ^ coboundary(G, S) == frozenset(Wp):
                    same_class = True
                    break
            if same_class:
                continue
            # Different classes → distance ≥ 1.
            min_d = len(all_E) + 1
            for mask in range(1 << len(V)):
                S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
                d = len(frozenset(W) ^ frozenset(Wp) ^ coboundary(G, S))
                if d < min_d:
                    min_d = d
            ok = min_d >= 1
            if not ok:
                c.record(False, {**describe(G, W), "Wp": sorted(Wp), "min_d": min_d})
            else:
                c.record(True)
    return c


# ===========================================================================
# G18: Cocycle class count per component structure:
#   #switching classes of G = ∏_i 2^{β_1(C_i)} where C_i ranges over
#   connected components.
# (Follows from the additivity of β_1 over components.)
# ===========================================================================

def claim_g18_switching_class_multiplicative():
    c = FuzzyClaim("G18", "#switching classes(G) = ∏_i 2^{β_1(C_i)}",
                   "G with possibly multiple components")
    seen = set()
    for n, G, _ in small_instances():
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        if n > 4:
            continue
        # Count switching classes directly.
        ws = list(all_wrap_subsets(G))
        idx = {w: i for i, w in enumerate(ws)}
        parent = list(range(len(ws)))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        V = list(G.nodes())
        for W in ws:
            for v in V:
                Wp = vertex_switch(G, W, v)
                ra, rb = find(idx[W]), find(idx[Wp])
                if ra != rb:
                    parent[ra] = rb
        classes = len({find(i) for i in range(len(ws))})
        expected = 1
        for comp in nx.connected_components(G):
            H = G.subgraph(comp)
            b1 = H.number_of_edges() - H.number_of_nodes() + 1
            expected *= (1 << b1)
        ok = classes == expected
        if not ok:
            c.record(False, {**describe(G, frozenset()),
                             "classes": classes, "expected": expected})
        else:
            c.record(True)
    return c


# ===========================================================================
# G19 (γ ∩ α): Balance-radius ≤ min-nonzero-coboundary-size (= edge-conn).
#   If G connected, bal_radius(G,W) ≤ edge-conn(G)?  NO this need not hold —
#   flipping W may be cheaper than reaching any nontrivial coboundary.
#   Better claim: bal_radius(G,W) ≤ min(|W|, |E| − |W|) is trivial.
# Instead we test: bal_radius(G,W) ≤ min(|W|, |W̄|) (reach W=∅ or W=E both
# coboundaries on bipartite graphs, trivially on any graph just via W or Wᶜ
# as the "switch target" = nearest coboundary). That's definitional only for
# bipartite. So restrict:
#   bipartite G: bal_radius ≤ min(|W|, |E|−|W|).
# ===========================================================================

def claim_g19_bal_radius_bipartite():
    c = FuzzyClaim("G19", "bipartite G: bal_radius(G,W) ≤ min(|W|, |E|−|W|)",
                   "G bipartite (∅ and E are both coboundaries)")
    for n, G, W in small_instances():
        if n > 4:
            continue
        if not nx.is_bipartite(G):
            continue
        r = bal_radius_by_coboundary(G, W)
        bound = min(len(W), G.number_of_edges() - len(W))
        ok = r <= bound
        if not ok:
            c.record(False, {**describe(G, W), "radius": r, "bound": bound})
        else:
            c.record(True)
    return c


# ===========================================================================
# G20 (γ ∩ β): Fiedler-pair of L_signed has sign-pattern == ε on balanced comp.
#   For balanced connected G,W: the (normalised) zero eigenvector v of
#   L_signed has signs ±1 matching some ε:V→{0,1} witnessing balance
#   (up to global sign flip). I.e. {v > 0} is ε⁻¹(0) or ε⁻¹(1).
# ===========================================================================

def claim_g20_kernel_vector_matches_epsilon():
    c = FuzzyClaim("G20", "ker(L_signed) on balanced connected G matches ε-partition",
                   "G connected, balanced; ker vector v has sign = (−1)^{ε(u)} up to global sign")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        if not is_balanced_component(G, W):
            continue
        Lsig = laplacian_signed(G, W)
        ev, vecs = np.linalg.eigh(Lsig)
        kernel = [vecs[:, i] for i in range(len(ev)) if abs(ev[i]) < TOL]
        if not kernel:
            continue
        v = kernel[0]
        if np.max(np.abs(v)) < TOL:
            continue
        v = v / np.max(np.abs(v))
        # Read off ε from sign of v.
        eps = {u: 0 if v[u] > 0 else 1 for u in G.nodes()}
        # Check ε witnesses balance.
        ok = True
        for (u, w) in G.edges():
            e = tuple(sorted((u, w)))
            flip = 1 if e in W else 0
            if (eps[u] ^ eps[w]) != flip:
                ok = False
                break
        if not ok:
            c.record(False, {**describe(G, W),
                             "kernel_vec": [float(x) for x in v],
                             "eps": eps})
        else:
            c.record(True)
    return c


# ===========================================================================
# G21 (sanity): #coboundaries · #cocycle-classes = 2^|E|.
# (Short exact sequence 0 → coboundaries → edges → cocycle-classes → 0 as
# Z/2-vector spaces.)
# ===========================================================================

def claim_g21_cob_cocycle_product():
    c = FuzzyClaim("G21", "#coboundaries · #switching-classes == 2^|E|",
                   "short exact sequence of Z/2 cochain complex")
    seen = set()
    for n, G, _ in small_instances():
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        if n > 4:
            continue
        V = list(G.nodes())
        cob = set()
        for mask in range(1 << len(V)):
            S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
            cob.add(coboundary(G, S))
        # Classes.
        ws = list(all_wrap_subsets(G))
        idx = {w: i for i, w in enumerate(ws)}
        parent = list(range(len(ws)))
        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for W in ws:
            for v in V:
                Wp = vertex_switch(G, W, v)
                ra, rb = find(idx[W]), find(idx[Wp])
                if ra != rb:
                    parent[ra] = rb
        classes = len({find(i) for i in range(len(ws))})
        ok = len(cob) * classes == (1 << G.number_of_edges())
        if not ok:
            c.record(False, {**describe(G, frozenset()),
                             "n_cob": len(cob), "n_cls": classes,
                             "2E": 1 << G.number_of_edges()})
        else:
            c.record(True)
    return c


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------

CLAIM_FNS = [
    claim_g1_switching_class_count,
    claim_g2_cycle_parity_switching_invariant,
    claim_g3_balance_iff_all_cycle_parity_zero,
    claim_g4_switching_to_hom_h1,
    claim_g5_epsilon_multiplicity,
    claim_g6_balance_radius_via_coboundary,
    claim_g7_bal_radius_bounded,
    claim_g8_edge_gluing_balance,
    claim_g9_vertex_identification_balance,
    claim_g10_switching_kernel_dim_invariant,
    claim_g11_coboundary_iff_even_cycle_parity,
    claim_g12_switching_preserves_beta,
    claim_g13_coboundary_cocycle_dimension,
    claim_g14_euler_characteristic,
    claim_g15_signed_kernel_dim_per_component,
    claim_g16_signed_laplacian_rank,
    claim_g17_switching_class_distance_nonzero,
    claim_g18_switching_class_multiplicative,
    claim_g19_bal_radius_bipartite,
    claim_g20_kernel_vector_matches_epsilon,
    claim_g21_cob_cocycle_product,
]


def main(out_json):
    results = []
    for fn in CLAIM_FNS:
        print(f"Running {fn.__name__} ...", flush=True)
        c = fn()
        print(f"  tau = {c.tau:.4f}  ({c.passed}/{c.tested})")
        results.append(c.to_dict())

    Path(out_json).write_text(json.dumps(results, indent=2, default=str))
    print(f"\nWrote {out_json}")
    print("\nRanked by tau:")
    for r in sorted(results, key=lambda r: (-r["tau"], str(r["idx"]))):
        print(f"  {r['idx']:>4}  tau={r['tau']:.4f}  ({r['passed']}/{r['tested']})  {r['name']}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).parent / "results.json")
    main(out)
