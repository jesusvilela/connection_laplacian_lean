"""
NEGATOR-FUZZY round 5: 21 NEW fuzzy claims about signed / covering
Laplacians, orthogonal to R3 (10 claims) and R4 (15 claims).

Claim sources for R5 (per cosmo-tree guidance):
  1. Trees/cycles/covers interactions (subdivision, contraction, bridges).
  2. Spectral-combinatorial interfaces (algebraic connectivity,
     spectral gap vs. wrap density).
  3. Double-cover derived identities (tr(L~^2), wedge identities).
  4. Kernel structure beyond dimension (fiber support, rank under
     fiber restriction).
  5. Cycle-space / H^1(G; Z/2) refinements.
  6. R4 near-miss promotions (C1 with non-bridge, C5 with Z/2 coboundary
     restriction, C15 with uniform Bernoulli graph measure).

For each claim C we compute tau(C) := P(C holds | preconditions), with
minimal counterexamples recorded when tau < 1. Search envelope matches
R4 (non-iso graphs on n in {3,4,5} with every wrap, plus n = 6 sample).

Output:
  - results.json : full record
  - report.md    : summary table (written by driver script, not here)
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
# Laplacian builders (identical to R3/R4).
# ---------------------------------------------------------------------------

def edge_list(G):
    return [tuple(sorted(e)) for e in G.edges()]


def laplacian_scalar(G):
    n = G.number_of_nodes()
    L = np.zeros((n, n))
    for u, v in G.edges():
        L[u, u] += 1
        L[v, v] += 1
        L[u, v] -= 1
        L[v, u] -= 1
    return L


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


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

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


def beta(G, wrap):
    return balanced_component_count(G, wrap)


def kernel_dim(M):
    ev = np.linalg.eigvalsh(M)
    return int(np.sum(np.abs(ev) < TOL))


def positive_eigs(M):
    ev = np.linalg.eigvalsh(M)
    return sorted(float(x) for x in ev if abs(x) > TOL)


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


def random_wrap(G, k=None):
    edges = edge_list(G)
    if k is None:
        k = RNG.randint(0, len(edges))
    sub = RNG.sample(edges, k) if k <= len(edges) else edges
    return frozenset(sub)


def relabel(G, W):
    """Relabel a subgraph to 0..n-1 and restrict wrap accordingly."""
    mapping = {old: new for new, old in enumerate(sorted(G.nodes()))}
    Gr = nx.relabel_nodes(G, mapping)
    Wr = frozenset(tuple(sorted((mapping[a], mapping[b])))
                   for (a, b) in W
                   if a in mapping and b in mapping)
    return Gr, Wr


def describe(G, W):
    return {"n": G.number_of_nodes(),
            "edges": edge_list(G),
            "wrap": sorted(list(W))}


def vertex_switch(G, W, v):
    new_W = set(W)
    for u in G.neighbors(v):
        e = tuple(sorted((u, v)))
        if e in new_W:
            new_W.discard(e)
        else:
            new_W.add(e)
    return frozenset(new_W)


def bridges(G):
    return set(tuple(sorted(e)) for e in nx.bridges(G))


def cycle_space_dim_Z2(G):
    """First Betti number = |E| - |V| + #components."""
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)


# ---------------------------------------------------------------------------
# Claim container
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
            tag = f"TRUE (fuzz-verified tau=1.0000, n={self.tested})"
        elif t > 0.9:
            tag = f"NEAR-TRUE (tau={t:.4f})"
        elif t > 0.5:
            tag = f"MOSTLY TRUE (tau={t:.4f})"
        elif t > 0.1:
            tag = f"MIXED (tau={t:.4f})"
        else:
            tag = f"COUNTEREXAMPLE-RICH (tau={t:.4f})"
        return tag

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
# Search envelope
# ---------------------------------------------------------------------------

def small_instances(n_min=3, n_max=5):
    for n in range(n_min, n_max + 1):
        for G in all_graphs_iso(n):
            for W in all_wrap_subsets(G):
                yield n, G, W


def medium_instances(n_min=3, n_max=6, wrap_cap=32):
    for n in range(n_min, n_max + 1):
        for G in all_graphs_iso(n):
            subs = list(all_wrap_subsets(G))
            if len(subs) > wrap_cap:
                subs = RNG.sample(subs, wrap_cap)
            for W in subs:
                yield n, G, W


# ===========================================================================
# Claim R1 (promotes R4-C1 with non-bridge hypothesis).
#   If e is a non-bridge, non-wrap edge of G, then beta(G,W) >= beta(G - e, W).
# ===========================================================================

def claim_r1_c1_nonbridge():
    c = FuzzyClaim("R1", "beta(G,W) >= beta(G-e,W) for non-bridge non-wrap e",
                   "e non-bridge, e not in W")
    for n, G, W in small_instances():
        br = bridges(G)
        for e in edge_list(G):
            if e in W:
                continue
            if e in br:
                continue
            Ge = G.copy()
            Ge.remove_edge(*e)
            b_G = beta(G, W)
            b_Ge = beta(Ge, W)
            ok = b_G >= b_Ge
            if not ok:
                c.record(False, {**describe(G, W), "removed_edge": list(e),
                                 "beta_G": b_G, "beta_G_minus_e": b_Ge})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R2: equality for non-bridge non-wrap deletion on connected G.
#   G connected, e non-bridge non-wrap => beta(G,W) == beta(G - e, W).
# (Stronger form of R1.)
# ===========================================================================

def claim_r2_c1_equality():
    c = FuzzyClaim("R2", "beta(G,W) == beta(G-e,W) for non-bridge non-wrap e on connected G",
                   "G connected, e non-bridge, e not in W")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        br = bridges(G)
        for e in edge_list(G):
            if e in W or e in br:
                continue
            Ge = G.copy()
            Ge.remove_edge(*e)
            b_G = beta(G, W)
            b_Ge = beta(Ge, W)
            ok = b_G == b_Ge
            if not ok:
                c.record(False, {**describe(G, W), "removed_edge": list(e),
                                 "beta_G": b_G, "beta_Ge": b_Ge})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R3 (promotes R4-C5 with coboundary restriction).
#   If W is a Z/2 coboundary (i.e. W = set of edges across some S subset V),
#   then beta(G, W) == beta(G, E \ W).
# Intuitively coboundary W's switch to W=empty and to W=E simultaneously
# (since E = coboundary(V) XOR identity on edges of... ). Claim scans.
# ===========================================================================

def is_coboundary(G, W):
    """W is a Z/2 coboundary iff exists S subset V with W == delta(S) = cut(S)."""
    V = list(G.nodes())
    E = set(edge_list(G))
    for mask in range(1 << len(V)):
        S = {V[i] for i in range(len(V)) if (mask >> i) & 1}
        cut = {tuple(sorted((u, v))) for (u, v) in G.edges() if (u in S) ^ (v in S)}
        if cut == set(W):
            return True
    return False


def claim_r3_c5_coboundary():
    c = FuzzyClaim("R3", "beta(G,W) == beta(G, E\\W) when W is a coboundary",
                   "W = delta(S) for some S (Z/2 coboundary)")
    for n, G, W in small_instances():
        if not is_coboundary(G, W):
            continue
        all_E = frozenset(edge_list(G))
        Wc = all_E - W
        b1 = beta(G, W)
        b2 = beta(G, Wc)
        ok = b1 == b2
        if not ok:
            c.record(False, {**describe(G, W),
                             "W_complement": sorted(Wc),
                             "beta_W": b1, "beta_Ec": b2})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R4 (C5 refined further):
#   For bipartite G, beta(G, W) == beta(G, E\W).
# On bipartite, E itself is a coboundary (cut of one color class), so E\W
# should behave like a switch of W.
# ===========================================================================

def claim_r4_c5_bipartite():
    c = FuzzyClaim("R4", "beta(G,W) == beta(G, E\\W) for bipartite G",
                   "G bipartite")
    for n, G, W in small_instances():
        if not nx.is_bipartite(G):
            continue
        all_E = frozenset(edge_list(G))
        Wc = all_E - W
        b1 = beta(G, W)
        b2 = beta(G, Wc)
        ok = b1 == b2
        if not ok:
            c.record(False, {**describe(G, W),
                             "beta_W": b1, "beta_Ec": b2})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R5 (promotes C15 with uniform graph measure):
#   Over uniform random connected graphs of fixed n and random wrap with
#   each edge independent Bernoulli(1/2), E[beta >= 1] decreases with |E|.
# We test an aggregate proxy: for fixed n, among all iso classes G on n
# vertices, Pr[beta >= 1] (uniform W) is non-increasing in |E(G)|.
# ===========================================================================

def claim_r5_c15_bernoulli():
    c = FuzzyClaim("R5", "Pr[beta>=1] non-increasing in |E| (uniform W, iso graphs)",
                   "averaged over iso classes on each n")
    for n in (3, 4, 5):
        bucket = {}  # m -> (passed_count, total_count)
        for G in all_graphs_iso(n):
            m = G.number_of_edges()
            for W in all_wrap_subsets(G):
                ok = beta(G, W) >= 1
                p, t = bucket.get(m, (0, 0))
                bucket[m] = (p + (1 if ok else 0), t + 1)
        keys = sorted(bucket)
        for i in range(len(keys) - 1):
            p_a = bucket[keys[i]][0] / max(1, bucket[keys[i]][1])
            p_b = bucket[keys[i + 1]][0] / max(1, bucket[keys[i + 1]][1])
            ok = p_a >= p_b - 1e-9
            if not ok:
                c.record(False, {"n": n, "m_lo": keys[i], "m_hi": keys[i + 1],
                                 "p_lo": p_a, "p_hi": p_b})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R6 (subdivision invariance):
#   Subdivide a non-wrap edge (u,v) via new vertex w with both new edges
#   non-wrap. Then beta(G, W) == beta(G', W').
# (Subdividing a non-wrap edge keeps signing the same trivially.)
# ===========================================================================

def subdivide_nonwrap(G, e, new_label):
    u, v = e
    Gp = G.copy()
    Gp.add_node(new_label)
    Gp.remove_edge(u, v)
    Gp.add_edge(u, new_label)
    Gp.add_edge(new_label, v)
    return Gp


def claim_r6_subdivision_nonwrap():
    c = FuzzyClaim("R6", "Subdividing a non-wrap edge preserves beta",
                   "e not in W; replace by path u-w-v with both new edges non-wrap")
    for n, G, W in small_instances():
        if n > 4:
            break  # keep this moderate
        new_label = n
        for e in edge_list(G):
            if e in W:
                continue
            Gp = subdivide_nonwrap(G, e, new_label)
            Wp = frozenset(W)  # new edges are non-wrap
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            ok = b1 == b2
            if not ok:
                c.record(False, {**describe(G, W), "subdivided_edge": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R7 (subdivision with wrap -> double non-wrap equals flip rule):
#   Subdividing a wrap edge (u,v) with both new edges non-wrap changes the
#   parity of every cycle through e, so beta may change. Instead claim:
#   subdividing wrap edge e with one of the two new edges as wrap preserves
#   beta. (Algebraic parity: 1 wrap becomes 1 wrap.)
# ===========================================================================

def subdivide_wrap_preserve_parity(G, W, e, new_label):
    u, v = e
    Gp = G.copy()
    Gp.add_node(new_label)
    Gp.remove_edge(u, v)
    e1 = tuple(sorted((u, new_label)))
    e2 = tuple(sorted((new_label, v)))
    Gp.add_edge(*e1)
    Gp.add_edge(*e2)
    Wp = set(W)
    Wp.discard(e)
    Wp.add(e1)  # new wrap edge
    return Gp, frozenset(Wp)


def claim_r7_subdivision_wrap():
    c = FuzzyClaim("R7", "Subdividing a wrap edge (1 new wrap + 1 new non-wrap) preserves beta",
                   "e in W; one of new edges is wrap, the other is not")
    for n, G, W in small_instances():
        if n > 4:
            break
        new_label = n
        for e in edge_list(G):
            if e not in W:
                continue
            Gp, Wp = subdivide_wrap_preserve_parity(G, W, e, new_label)
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            ok = b1 == b2
            if not ok:
                c.record(False, {**describe(G, W), "subdivided_edge": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R8 (bridge contraction preserves beta):
#   If e = (u,v) is a bridge in G (non-wrap), contract e. Then
#   beta(G, W) == beta(G / e, W').
# ===========================================================================

def contract_edge_nonwrap(G, W, e):
    u, v = e
    Gp = G.copy()
    Gp = nx.contracted_edge(Gp, (u, v), self_loops=False)
    # Relabel: v is merged into u.
    Wp = set()
    for a, b in W:
        if a == v:
            a = u
        if b == v:
            b = u
        if a != b:
            Wp.add(tuple(sorted((a, b))))
    return Gp, frozenset(Wp)


def claim_r8_bridge_contraction():
    c = FuzzyClaim("R8", "Contracting a bridge non-wrap edge preserves beta",
                   "e bridge, e not in W")
    for n, G, W in small_instances():
        if n > 4:
            break
        br = bridges(G)
        for e in edge_list(G):
            if e in W or e not in br:
                continue
            Gp, Wp = contract_edge_nonwrap(G, W, e)
            if Gp.number_of_nodes() < 1:
                continue
            Gp2, Wp2 = relabel(Gp, Wp)
            b1 = beta(G, W)
            b2 = beta(Gp2, Wp2)
            ok = b1 == b2
            if not ok:
                c.record(False, {**describe(G, W), "contracted_edge": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R9 (algebraic connectivity vs. balance):
#   Define lambda_2(L_scalar) = algebraic connectivity (second-smallest eig).
#   Claim: lambda_2(L_signed) >= 0 always (i.e. L_signed second-smallest
#   eigenvalue is nonneg). Equivalent to L_signed PSD.
# ===========================================================================

def claim_r9_alg_connectivity_signed():
    c = FuzzyClaim("R9", "lambda_2(L_signed) >= 0 (L_signed PSD, 2nd eig)",
                   "any G,W")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        ev = sorted(np.linalg.eigvalsh(Lsig))
        second = ev[1] if len(ev) >= 2 else ev[0]
        ok = second >= -TOL
        if not ok:
            c.record(False, {**describe(G, W), "second_eig": float(second)})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R10 (spectral gap vs. wrap density):
#   For connected G with |W| = 0, spec gap = lambda_2(L_signed) = lambda_2(L_scalar).
#   When |W| > 0 and G connected and balanced, same holds on balanced component.
# Formalised claim: lambda_1(L_signed) = 0 iff G has >= 1 balanced component.
# ===========================================================================

def claim_r10_gap_zero_iff_balanced():
    c = FuzzyClaim("R10", "lambda_min(L_signed) == 0 iff beta >= 1",
                   "any G,W")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        ev = np.linalg.eigvalsh(Lsig)
        has_zero = bool(np.min(np.abs(ev)) < TOL)
        bal = beta(G, W) >= 1
        ok = (has_zero == bal)
        if not ok:
            c.record(False, {**describe(G, W),
                             "min_eig": float(np.min(ev)),
                             "beta": beta(G, W)})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R11 (tr(L_mob^2) decomposition):
#   tr(L_mob^2) == tr(L_scalar^2) + tr(L_signed^2).
# ===========================================================================

def claim_r11_trace_sq_decomposes():
    c = FuzzyClaim("R11", "tr(L_mob^2) == tr(L_scalar^2) + tr(L_signed^2)",
                   "any G,W")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        lhs = float(np.trace(Lm @ Lm))
        rhs = float(np.trace(Ls @ Ls) + np.trace(Lsig @ Lsig))
        ok = abs(lhs - rhs) < 1e-6
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R12 (tr(L_mob^k) decomposition for k=3,4):
#   tr(L_mob^k) == tr(L_scalar^k) + tr(L_signed^k).
# ===========================================================================

def claim_r12_trace_cube_decomposes():
    c = FuzzyClaim("R12", "tr(L_mob^k) == tr(L_scalar^k) + tr(L_signed^k) for k in {3,4}",
                   "any G,W")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        for k in (3, 4):
            Lm_k = np.linalg.matrix_power(Lm, k)
            Ls_k = np.linalg.matrix_power(Ls, k)
            Lsig_k = np.linalg.matrix_power(Lsig, k)
            lhs = float(np.trace(Lm_k))
            rhs = float(np.trace(Ls_k) + np.trace(Lsig_k))
            ok = abs(lhs - rhs) < 1e-5 * (1 + abs(lhs) + abs(rhs))
            if not ok:
                c.record(False, {**describe(G, W), "k": k, "lhs": lhs, "rhs": rhs})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R13 (kernel basis support: sign-alternating ker vector on balanced
# component realises +/-1 values). For balanced component C, L_signed has
# a kernel vector supported on C whose entries are all +/- 1 up to scale.
# ===========================================================================

def claim_r13_pm1_kernel_support():
    c = FuzzyClaim("R13", "ker(L_signed) has +/- 1 basis vector per balanced component",
                   "beta >= 1; check each balanced component yields +/-1 kernel vector")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        if not is_balanced_component(G, W):
            continue
        Lsig = laplacian_signed(G, W)
        ev, vecs = np.linalg.eigh(Lsig)
        # Kernel vectors (|ev| small):
        kernel_vecs = [vecs[:, i] for i in range(len(ev)) if abs(ev[i]) < TOL]
        if not kernel_vecs:
            continue
        v = kernel_vecs[0]
        # Normalise so max |entry| = 1
        if np.max(np.abs(v)) < TOL:
            continue
        v = v / np.max(np.abs(v))
        # Check each entry is close to +/- 1
        ok = bool(np.all(np.abs(np.abs(v) - 1.0) < 1e-5))
        if not ok:
            c.record(False, {**describe(G, W),
                             "normalized_kernel_vec": [float(x) for x in v]})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R14 (fiber restriction rank): for each connected component C, the
# principal submatrix of L_mob indexed by the lifts V(C) x {0,1} has rank
# 2*|C| - (1 + [C balanced]).
# ===========================================================================

def claim_r14_fiber_restriction_rank():
    c = FuzzyClaim("R14", "rank(L_mob restricted to fiber over C) = 2|C| - (1+[C balanced])",
                   "C is a connected component")
    for n, G, W in small_instances():
        for comp in nx.connected_components(G):
            H = G.subgraph(comp).copy()
            Hrl, Wrl = relabel(H, W)
            Lm = laplacian_mobius(Hrl, Wrl)
            r = int(np.linalg.matrix_rank(Lm, tol=TOL))
            size = 2 * Hrl.number_of_nodes()
            expected = size - (1 + (1 if is_balanced_component(Hrl, Wrl) else 0))
            ok = r == expected
            if not ok:
                c.record(False, {**describe(G, W),
                                 "component": sorted(comp),
                                 "rank": r, "expected": expected})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R15 (cycle-space / H^1(G; Z/2) generator count):
#   dim H^1(G; Z/2) == #{independent cycles} = |E| - |V| + #comps.
# Claim: #{wrap subsets W with G balanced} == 2^(|V| - #comps).
# (Balance iff wrap is a coboundary, which is a 2^(|V|-c)-dimensional
# subspace of 2^|E| edge subsets.)
# ===========================================================================

def claim_r15_coboundary_count():
    c = FuzzyClaim("R15", "#{W : G balanced} == 2^(|V|-#comps)",
                   "any connected component structure")
    seen = set()
    for n, G, _ in small_instances():
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        n_comp = nx.number_connected_components(G)
        expected = 1 << (G.number_of_nodes() - n_comp)
        count = 0
        for W in all_wrap_subsets(G):
            if balanced_component_count(G, W) == n_comp:
                # All components balanced = globally balanced.
                count += 1
        ok = count == expected
        if not ok:
            c.record(False, {**describe(G, frozenset()),
                             "count": count, "expected": expected})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R16 (cocycle min support size):
#   For connected G, the minimum nonzero coboundary has |delta(S)| >=
#   edge-connectivity of G.
# ===========================================================================

def claim_r16_min_cocycle_support():
    c = FuzzyClaim("R16", "min nonzero coboundary size == edge-connectivity",
                   "G connected, n >= 2")
    seen = set()
    for n, G, _ in small_instances():
        if not nx.is_connected(G) or G.number_of_nodes() < 2:
            continue
        key = (n, frozenset(edge_list(G)))
        if key in seen:
            continue
        seen.add(key)
        E = set(edge_list(G))
        n_nodes = G.number_of_nodes()
        min_cut = math.inf
        for mask in range(1, (1 << n_nodes) - 1):
            S = {v for v in G.nodes() if (mask >> v) & 1}
            if not S or S == set(G.nodes()):
                continue
            cut = {tuple(sorted((u, v))) for (u, v) in G.edges() if (u in S) ^ (v in S)}
            if cut:
                min_cut = min(min_cut, len(cut))
        ec = nx.edge_connectivity(G)
        ok = (min_cut == ec)
        if not ok:
            c.record(False, {**describe(G, frozenset()), "min_cut": min_cut, "ec": ec})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R17 (interlacing): removing a non-wrap edge interlaces spectra:
#   lambda_i(L_signed(G - e, W)) <= lambda_i(L_signed(G, W)) <= lambda_{i+1}(L_signed(G - e, W)).
# (Standard interlacing for rank-2 PSD perturbation.)
# ===========================================================================

def claim_r17_interlacing():
    c = FuzzyClaim("R17", "spectral interlacing under non-wrap edge removal (L_signed)",
                   "e not in W")
    for n, G, W in small_instances():
        for e in edge_list(G):
            if e in W:
                continue
            Ge = G.copy()
            Ge.remove_edge(*e)
            Ls_G = laplacian_signed(G, W)
            Ls_Ge = laplacian_signed(Ge, W)
            ev_G = sorted(np.linalg.eigvalsh(Ls_G))
            ev_Ge = sorted(np.linalg.eigvalsh(Ls_Ge))
            ok = True
            for i in range(len(ev_G) - 1):
                if not (ev_Ge[i] - 1e-6 <= ev_G[i] <= ev_Ge[i + 1] + 1e-6):
                    ok = False
                    break
            if not ok:
                c.record(False, {**describe(G, W), "removed_edge": list(e),
                                 "ev_G": [float(x) for x in ev_G],
                                 "ev_Ge": [float(x) for x in ev_Ge]})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R18 (trace bound): tr(L_signed) == 2|E| == tr(L_scalar).
# ===========================================================================

def claim_r18_trace_equal():
    c = FuzzyClaim("R18", "tr(L_signed) == tr(L_scalar) == 2|E|",
                   "any G,W")
    for n, G, W in small_instances():
        tr_s = float(np.trace(laplacian_scalar(G)))
        tr_sig = float(np.trace(laplacian_signed(G, W)))
        ok = abs(tr_s - tr_sig) < 1e-9 and abs(tr_s - 2 * G.number_of_edges()) < 1e-9
        if not ok:
            c.record(False, {**describe(G, W), "tr_s": tr_s, "tr_sig": tr_sig,
                             "2m": 2 * G.number_of_edges()})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R19 (sum of squared eigenvalues identity for the cover):
#   sum eigenvalues(L_mob)^2 == 2 * sum deg^2 + 4|E|.
# Since L_mob diag blocks sum to deg*I and off-diag blocks are +/- 1 / X,
# the Frobenius norm squared equals 2*sum deg^2 (diag) + 4|E| (off-diag,
# counting both block entries of each edge twice in each direction).
# ===========================================================================

def claim_r19_frobenius_mob():
    c = FuzzyClaim("R19", "||L_mob||_F^2 == 2*sum(deg^2) + 4|E|",
                   "any G,W")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        lhs = float(np.sum(Lm * Lm))
        deg = dict(G.degree())
        rhs = 2 * sum(d * d for d in deg.values()) + 4 * G.number_of_edges()
        ok = abs(lhs - rhs) < 1e-6
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R20 (disjoint union decomposes kernel):
#   beta(G1 U G2, W1 U W2) == beta(G1, W1) + beta(G2, W2).
# ===========================================================================

def disjoint_union(G1, W1, G2, W2):
    n1 = G1.number_of_nodes()
    G = nx.Graph()
    G.add_nodes_from(range(n1 + G2.number_of_nodes()))
    G.add_edges_from(G1.edges())
    for (u, v) in G2.edges():
        G.add_edge(u + n1, v + n1)
    W = set(W1)
    for (u, v) in W2:
        W.add(tuple(sorted((u + n1, v + n1))))
    return G, frozenset(W)


def claim_r20_disjoint_union():
    c = FuzzyClaim("R20", "beta(G1 U G2, W1 U W2) == beta(G1,W1) + beta(G2,W2)",
                   "disjoint union")
    # Enumerate pairs of small iso graphs on n1, n2 <= 3.
    pairs = []
    for n1 in (2, 3):
        for n2 in (2, 3):
            for G1 in all_graphs_iso(n1):
                for G2 in all_graphs_iso(n2):
                    pairs.append((G1, G2))
    RNG.shuffle(pairs)
    for G1, G2 in pairs[:60]:
        W1s = list(all_wrap_subsets(G1))
        W2s = list(all_wrap_subsets(G2))
        # sample a few wrap pairs
        for _ in range(4):
            W1 = RNG.choice(W1s)
            W2 = RNG.choice(W2s)
            G, W = disjoint_union(G1, W1, G2, W2)
            lhs = beta(G, W)
            rhs = beta(G1, W1) + beta(G2, W2)
            ok = lhs == rhs
            if not ok:
                c.record(False, {"G1": edge_list(G1), "W1": sorted(W1),
                                 "G2": edge_list(G2), "W2": sorted(W2),
                                 "lhs": lhs, "rhs": rhs})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim R21 (balanced-implies-bipartite-via-wrap): if G is connected and W
# is balanced signing, then (V, W) is a bipartite graph (as a simple graph).
# That is, the wrap-subgraph has no odd cycles.
# ===========================================================================

def claim_r21_wrap_bipartite():
    c = FuzzyClaim("R21", "connected G balanced => wrap subgraph (V,W) is bipartite",
                   "G connected, balanced")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        if not is_balanced_component(G, W):
            continue
        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        H.add_edges_from(W)
        ok = nx.is_bipartite(H)
        if not ok:
            c.record(False, {**describe(G, W)})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim R22 (wedge/sum identity across fiber swap):
#   ker(L_mob) decomposes as span{(v, v)} for v in ker(L_scalar) and
#   span{(v, -v)} for v in ker(L_signed) (after re-ordering coordinates by
#   vertex then fiber). Claim: the two kernel subspaces are orthogonal.
# ===========================================================================

def claim_r22_fiber_kernel_orthogonal():
    c = FuzzyClaim("R22", "ker(L_mob) splits as orthogonal (sym, anti) spaces",
                   "for any G,W: sym ker = lift of ker(L_scalar); anti ker = lift of ker(L_signed)")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        n_nodes = G.number_of_nodes()
        # Lift kernel vectors of L_scalar: (x, x) pattern.
        _, vs = np.linalg.eigh(Ls)
        _, vsig = np.linalg.eigh(Lsig)
        eig_s = np.linalg.eigvalsh(Ls)
        eig_sig = np.linalg.eigvalsh(Lsig)
        ker_s = [vs[:, i] for i in range(n_nodes) if abs(eig_s[i]) < TOL]
        ker_sig = [vsig[:, i] for i in range(n_nodes) if abs(eig_sig[i]) < TOL]
        # Build sym/anti lifts: each vertex u has components 2u, 2u+1.
        def sym_lift(v):
            out = np.zeros(2 * n_nodes)
            for u in range(n_nodes):
                out[2 * u] = v[u]
                out[2 * u + 1] = v[u]
            return out / np.linalg.norm(out) if np.linalg.norm(out) > TOL else out

        def anti_lift(v):
            out = np.zeros(2 * n_nodes)
            for u in range(n_nodes):
                out[2 * u] = v[u]
                out[2 * u + 1] = -v[u]
            return out / np.linalg.norm(out) if np.linalg.norm(out) > TOL else out

        sym = [sym_lift(v) for v in ker_s]
        anti = [anti_lift(v) for v in ker_sig]
        # Verify all sym and anti are in ker(L_mob) AND mutually orthogonal.
        ok = True
        for s in sym:
            if np.linalg.norm(Lm @ s) > 1e-5:
                ok = False
                break
        if ok:
            for a in anti:
                if np.linalg.norm(Lm @ a) > 1e-5:
                    ok = False
                    break
        if ok:
            for s in sym:
                for a in anti:
                    if abs(np.dot(s, a)) > 1e-6:
                        ok = False
                        break
        if not ok:
            c.record(False, {**describe(G, W)})
        else:
            c.record(True)
    return c


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

CLAIM_FNS = [
    claim_r1_c1_nonbridge,
    claim_r2_c1_equality,
    claim_r3_c5_coboundary,
    claim_r4_c5_bipartite,
    claim_r5_c15_bernoulli,
    claim_r6_subdivision_nonwrap,
    claim_r7_subdivision_wrap,
    claim_r8_bridge_contraction,
    claim_r9_alg_connectivity_signed,
    claim_r10_gap_zero_iff_balanced,
    claim_r11_trace_sq_decomposes,
    claim_r12_trace_cube_decomposes,
    claim_r13_pm1_kernel_support,
    claim_r14_fiber_restriction_rank,
    claim_r15_coboundary_count,
    claim_r16_min_cocycle_support,
    claim_r17_interlacing,
    claim_r18_trace_equal,
    claim_r19_frobenius_mob,
    claim_r20_disjoint_union,
    claim_r21_wrap_bipartite,
    claim_r22_fiber_kernel_orthogonal,
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
        print(f"  {r['idx']:>3}  tau={r['tau']:.4f}  ({r['passed']}/{r['tested']})  {r['name']}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).parent / "results.json")
    main(out)
