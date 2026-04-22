"""
NEGATOR-A Round 6, SHEAF-SECTION BETA (spectral / trace / eigenvalue / norm).

New fuzzy claims about spectral invariants of the three Laplacians
(L_s = scalar, L_sig = signed, L_mob = Moebius cover) on connection graphs.
All claims here are orthogonal to the R5 beta-tile landings:
  - R9  (L_sig PSD)            landed as L13_PSD
  - R11/R12 (tr L_mob^k split, k=2,3,4)
  - R17 (Cauchy interlacing under non-wrap edge removal)
  - R18 (tr L_sig = tr L_s = 2|E|)
  - R19 (||L_mob||_F^2 identity)

We therefore push into k >= 5 trace power sums, mixed traces, operator
norms, eigenvalue orderings, spectral gap identities, matrix-function
invariants, and interlacing sharpenings.

Envelope: all non-iso ConnGraphs on n in {3,4,5} with every wrap subset,
plus a deterministic sample on n = 6 (20 iso-classes x 20 wraps).

Output: results_beta.json and a summary table printed to stdout.
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
RNG = random.Random(20260422 + 6)  # R6 seed


# ---------------------------------------------------------------------------
# Laplacian builders (copied from R5 fuzz_r5.py for reproducibility).
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
# Graph combinatorics helpers
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


def beta(G, W):
    return balanced_component_count(G, W)


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


def small_instances(n_min=3, n_max=5):
    for n in range(n_min, n_max + 1):
        for G in all_graphs_iso(n):
            for W in all_wrap_subsets(G):
                yield n, G, W


def n6_sample(iso_cap=20, wrap_cap=20, n=6):
    """Deterministic sample on n=6."""
    classes = list(all_graphs_iso(n))
    if len(classes) > iso_cap:
        classes = RNG.sample(classes, iso_cap)
    for G in classes:
        subs = list(all_wrap_subsets(G))
        if len(subs) > wrap_cap:
            subs = RNG.sample(subs, wrap_cap)
        for W in subs:
            yield n, G, W


# ---------------------------------------------------------------------------
# Spectral helpers
# ---------------------------------------------------------------------------

def eigs_sorted(M):
    return sorted(float(x) for x in np.linalg.eigvalsh(M))


def trace_power(M, k):
    return float(np.trace(np.linalg.matrix_power(M, k)))


def frob_sq(M):
    return float(np.sum(M * M))


def op_norm(M):
    """Spectral / operator norm for a symmetric real matrix."""
    ev = np.linalg.eigvalsh(M)
    return float(np.max(np.abs(ev)))


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


# ===========================================================================
# B1  Higher trace power-sums:  tr(L_mob^k) = tr(L_s^k) + tr(L_sig^k) for
#      k in {5,6,7,8}.  R5/R12 covered k in {3,4}; R11 covered k=2.  Pattern
#      conjecture: holds for all k >= 0.
# ===========================================================================

def claim_b1_higher_trace_split():
    c = FuzzyClaim("B1", "tr(L_mob^k)=tr(L_s^k)+tr(L_sig^k) for k in {5,6,7,8}",
                   "any G, any W")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        for k in (5, 6, 7, 8):
            lhs = trace_power(Lm, k)
            rhs = trace_power(Ls, k) + trace_power(Lsig, k)
            scale = 1.0 + abs(lhs) + abs(rhs)
            ok = abs(lhs - rhs) < 1e-5 * scale
            if not ok:
                c.record(False, {**describe(G, W), "k": k,
                                 "lhs": lhs, "rhs": rhs})
            else:
                c.record(True)
    return c


# ===========================================================================
# B2  Mixed trace vanishes:  tr(L_s . L_sig) = tr(L_s^2).
#      Because L_sig = D - A_sig, L_s = D - A, and A and A_sig share the
#      same diagonal of zeros, but off-diagonals differ.  Conjecture to
#      probe: tr(L_s L_sig) = 2m + tr(A A_sig).  Since tr(A A_sig) = sum
#      over edges of (sign of that edge) = #nonwrap - #wrap = m - 2|W|.
#      So tr(L_s L_sig) = 2m + m - 2|W| = 3m - 2|W|? Check.
#  Let's define the RHS exactly and test.
# ===========================================================================

def claim_b2_mixed_s_sig():
    c = FuzzyClaim("B2", "tr(L_s * L_sig) = sum_u deg(u)^2 + 2*m - 4*|W|",
                   "any G, any W")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        lhs = float(np.trace(Ls @ Lsig))
        m = G.number_of_edges()
        w = len(W)
        deg = dict(G.degree())
        # Derivation:  tr((D-A)(D-A_sig)) = tr(D^2) - tr(D A_sig) - tr(A D) + tr(A A_sig).
        # tr(D^2) = sum deg^2; tr(D A_sig) = 0 (A_sig zero on diag); tr(A D) = 0;
        # tr(A A_sig) = sum_{uv} A_{uv} A_sig_{uv} = 2*(#nonwrap - #wrap) = 2*(m - 2w).
        rhs = sum(d * d for d in deg.values()) + 2 * (m - 2 * w)
        ok = abs(lhs - rhs) < 1e-6 * (1 + abs(lhs))
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# B3  Mixed trace tr(L_s . L_mob) = 2 * tr(L_s^2).
#      Because L_mob restricted to symmetric fibre acts as L_s tensor I_2
#      plus cross-terms.  Precisely:  L_mob = L_s (x) I_2 + (sigma-part).
#      Claim: tr(L_s (x) I_2 . L_mob) = 2 * tr(L_s . (sym part of L_mob)).
#      Simpler to test: define lift L_s^{up} = L_s kron I_2; claim
#      tr(L_s^{up} . L_mob) = 2 * tr(L_s^2).
# ===========================================================================

def claim_b3_mixed_s_mob_lift():
    c = FuzzyClaim("B3", "tr((L_s (x) I_2) . L_mob) = 2 * tr(L_s^2)",
                   "any G, any W")
    I2 = np.eye(2)
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lm = laplacian_mobius(G, W)
        Ls_up = np.kron(Ls, I2)
        lhs = float(np.trace(Ls_up @ Lm))
        rhs = 2.0 * trace_power(Ls, 2)
        ok = abs(lhs - rhs) < 1e-6 * (1 + abs(lhs))
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# B4  Trace-power positivity:  tr(L_sig^{2k}) >= 0 for all k, and
#      tr(L_sig^{2k}) >= tr(L_sig^{2k+1}) for connected G (since PSD).
#      This would be trivial for PSD; L_sig IS PSD per L13_PSD.  Test
#      anyway for k=1..4 as sanity / double check.
# ===========================================================================

def claim_b4_trace_power_monotone():
    c = FuzzyClaim("B4", "tr(L_sig^(k+1)) <= tr(L_sig^k) * ||L_sig||_op",
                   "any G, any W (Perron-style monotonicity for PSD)")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        lam = op_norm(Lsig)
        for k in (1, 2, 3):
            tk = trace_power(Lsig, k)
            tk1 = trace_power(Lsig, k + 1)
            rhs = tk * lam
            # Inequality tk1 <= rhs, up to tolerance.
            ok = tk1 <= rhs + 1e-6 * (1 + abs(rhs))
            if not ok:
                c.record(False, {**describe(G, W), "k": k,
                                 "tk": tk, "tk1": tk1, "lam": lam})
            else:
                c.record(True)
    return c


# ===========================================================================
# B5  Eigenvalue ordering: lambda_max(L_sig) <= lambda_max(L_s).
#     (Signed Laplacian cannot exceed scalar Laplacian in spectral radius
#      since diag is the same and off-diag has magnitude <= 1 entrywise,
#      with same Frobenius on off-diag.)
#      Counterexample-sensitive; test.
# ===========================================================================

def claim_b5_lambda_max_order():
    c = FuzzyClaim("B5", "lambda_max(L_sig) <= lambda_max(L_s)",
                   "any G, any W")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        lmax_s = max(np.linalg.eigvalsh(Ls))
        lmax_sig = max(np.linalg.eigvalsh(Lsig))
        ok = lmax_sig <= lmax_s + 1e-6
        if not ok:
            c.record(False, {**describe(G, W),
                             "lmax_s": float(lmax_s),
                             "lmax_sig": float(lmax_sig)})
        else:
            c.record(True)
    return c


# ===========================================================================
# B6  Eigenvalue ordering:  lambda_max(L_mob) = max(lambda_max(L_s),
#                                                   lambda_max(L_sig)).
#     Because L_mob block-diagonalises into L_s (sym) plus L_sig (anti)
#     after orthogonal change of basis in each fibre; spectra unite.
# ===========================================================================

def claim_b6_lambda_max_mob_equals_max():
    c = FuzzyClaim("B6", "lambda_max(L_mob) = max(lambda_max(L_s), lambda_max(L_sig))",
                   "any G, any W")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        lmax_m = max(np.linalg.eigvalsh(Lm))
        rhs = max(max(np.linalg.eigvalsh(Ls)), max(np.linalg.eigvalsh(Lsig)))
        ok = abs(lmax_m - rhs) < 1e-6 * (1 + abs(rhs))
        if not ok:
            c.record(False, {**describe(G, W),
                             "lmax_m": float(lmax_m),
                             "rhs": float(rhs)})
        else:
            c.record(True)
    return c


# ===========================================================================
# B7  Spectrum(L_mob) = Spectrum(L_s) multiset-union Spectrum(L_sig).
#     Strongest form of B6.  If true, ALL spectral invariants of L_mob
#     can be reduced to the two smaller Laplacians (fundamental for the
#     Moebius-cover story).
# ===========================================================================

def claim_b7_spectrum_union():
    c = FuzzyClaim("B7", "spec(L_mob) = spec(L_s) U spec(L_sig) (multiset)",
                   "any G, any W")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        ev_m = sorted(np.linalg.eigvalsh(Lm))
        ev_union = sorted(list(np.linalg.eigvalsh(Ls)) + list(np.linalg.eigvalsh(Lsig)))
        if len(ev_m) != len(ev_union):
            c.record(False, {**describe(G, W), "reason": "size mismatch"})
            continue
        diffs = [abs(a - b) for a, b in zip(ev_m, ev_union)]
        ok = max(diffs) < 1e-5
        if not ok:
            c.record(False, {**describe(G, W),
                             "ev_m": [float(x) for x in ev_m],
                             "ev_union": [float(x) for x in ev_union],
                             "max_diff": max(diffs)})
        else:
            c.record(True)
    return c


# ===========================================================================
# B8  Algebraic connectivity vs spectral gap of signed:
#      On connected G, lambda_2(L_s) (= alg connectivity) >= lambda_min(L_sig)
#      with equality iff W is empty (or a coboundary).
#  Also: lambda_2(L_s) >= lambda_min(L_sig) always.  Test inequality.
# ===========================================================================

def claim_b8_alg_conn_bounds_sig():
    c = FuzzyClaim("B8", "lambda_2(L_s) >= lambda_min(L_sig) on connected G",
                   "G connected")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        ev_s = sorted(np.linalg.eigvalsh(Ls))
        ev_sig = sorted(np.linalg.eigvalsh(Lsig))
        # lambda_2(L_s) is ev_s[1]; lambda_min(L_sig) is ev_sig[0].
        if len(ev_s) < 2:
            continue
        l2 = ev_s[1]
        lmin_sig = ev_sig[0]
        ok = l2 + 1e-6 >= lmin_sig
        if not ok:
            c.record(False, {**describe(G, W),
                             "lambda_2_s": float(l2),
                             "lambda_min_sig": float(lmin_sig)})
        else:
            c.record(True)
    return c


# ===========================================================================
# B9  Characteristic-poly coefficient identity:  c_{n-1}(L_s) = 2m
#      (already known).  Claim:  c_{n-1}(L_sig) = 2m (same).  And more:
#      c_{n-2}(L_sig) = 2*(sum_{u<v} deg(u)*deg(v) - sum of deg - #W).
#      Complicated -- simpler: c_{2n-1}(L_mob) = 4m (= tr(L_mob)).
#      Test the very clean one:  det(L_mob) = 0 iff connected component
#      is NOT all unbalanced; more precisely,
#           dim ker L_mob = #comps + #balanced-comps.
# ===========================================================================

def claim_b9_kernel_dim_mob_count():
    c = FuzzyClaim("B9", "dim ker(L_mob) = #components(G) + beta(G,W)",
                   "any G, any W")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        ev = np.linalg.eigvalsh(Lm)
        ker_dim = int(np.sum(np.abs(ev) < TOL))
        rhs = nx.number_connected_components(G) + beta(G, W)
        ok = ker_dim == rhs
        if not ok:
            c.record(False, {**describe(G, W),
                             "ker_dim": ker_dim, "rhs": rhs,
                             "ev": [float(x) for x in sorted(ev)]})
        else:
            c.record(True)
    return c


# ===========================================================================
# B10  Operator norm comparison:  ||L_sig||_op <= ||L_s||_op.
#      Corollary/refinement of B5.  L_sig is PSD (per L13_PSD) so
#      ||L_sig||_op = lambda_max(L_sig).  L_s is PSD, so ||L_s||_op =
#      lambda_max(L_s).  So equivalent to B5, but logged separately for
#      Lean-theorem naming clarity.
# ===========================================================================

def claim_b10_op_norm_sig_le_s():
    c = FuzzyClaim("B10", "||L_sig||_op <= ||L_s||_op",
                   "any G, any W")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        lhs = op_norm(Lsig)
        rhs = op_norm(Ls)
        ok = lhs <= rhs + 1e-6
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# B11  Eigenvector support encodes balanced structure:  for each unit
#      eigenvector v of L_sig with eigenvalue 0, the set
#        { u : v[u] != 0 }  equals a union of balanced components.
#      (Standard corollary of the R5 R13 +/-1 basis claim and
#       block-diagonal structure of L_sig across components.)
# ===========================================================================

def claim_b11_ker_support_is_balanced_union():
    c = FuzzyClaim("B11", "support(v in ker L_sig) = union of balanced comps",
                   "any G, any W")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        ev, vecs = np.linalg.eigh(Lsig)
        comps = list(nx.connected_components(G))
        balanced_comps = []
        for comp in comps:
            H = G.subgraph(comp).copy()
            He = set(tuple(sorted(e)) for e in H.edges())
            if is_balanced_component(H, W & He):
                balanced_comps.append(comp)
        for i in range(len(ev)):
            if abs(ev[i]) > TOL:
                continue
            v = vecs[:, i]
            supp = {u for u in range(len(v)) if abs(v[u]) > 1e-6}
            # Support must be a disjoint union of balanced components.
            remaining = set(supp)
            ok = True
            for comp in balanced_comps:
                cs = set(comp)
                if cs.issubset(remaining):
                    remaining -= cs
                elif cs & remaining:
                    # Partial overlap but not full component -- forbidden.
                    ok = False
                    break
            if remaining:
                ok = False
            if not ok:
                c.record(False, {**describe(G, W),
                                 "eig_idx": i,
                                 "support": sorted(supp),
                                 "balanced_comps": [sorted(c) for c in balanced_comps]})
            else:
                c.record(True)
    return c


# ===========================================================================
# B12  Exponential trace identity: tr(exp(-t L_mob)) = tr(exp(-t L_s))
#       + tr(exp(-t L_sig)) for all t > 0.
#      Follows immediately from B7 (spectrum union) if that's true.
#      Numerical sanity at t = 0.5 and t = 2.0.
# ===========================================================================

def claim_b12_heat_trace_split():
    c = FuzzyClaim("B12", "tr(exp(-t L_mob)) = tr(exp(-t L_s)) + tr(exp(-t L_sig))",
                   "t in {0.5, 2.0}")
    from scipy.linalg import expm  # defer import
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        for t in (0.5, 2.0):
            lhs = float(np.trace(expm(-t * Lm)))
            rhs = float(np.trace(expm(-t * Ls))) + float(np.trace(expm(-t * Lsig)))
            ok = abs(lhs - rhs) < 1e-5 * (1 + abs(rhs))
            if not ok:
                c.record(False, {**describe(G, W), "t": t,
                                 "lhs": lhs, "rhs": rhs})
            else:
                c.record(True)
    return c


# ===========================================================================
# B13  Resolvent trace split: for z not in spectrum,
#      tr((z I - L_mob)^{-1}) = tr((z I - L_s)^{-1}) + tr((z I - L_sig)^{-1}).
#      Again immediate from B7 if true; tested at z = -1 (safely off-spectrum
#      since spectra are >= 0).
# ===========================================================================

def claim_b13_resolvent_split():
    c = FuzzyClaim("B13", "tr((zI-L_mob)^{-1}) = tr((zI-L_s)^{-1}) + tr((zI-L_sig)^{-1})",
                   "z = -1")
    z = -1.0
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        nn = Ls.shape[0]
        try:
            Rs = np.linalg.inv(z * np.eye(nn) - Ls)
            Rsig = np.linalg.inv(z * np.eye(nn) - Lsig)
            Rm = np.linalg.inv(z * np.eye(2 * nn) - Lm)
        except np.linalg.LinAlgError:
            continue
        lhs = float(np.trace(Rm))
        rhs = float(np.trace(Rs)) + float(np.trace(Rsig))
        ok = abs(lhs - rhs) < 1e-5 * (1 + abs(rhs))
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# B14  Interlacing sharpening: removing a WRAP edge from W (not removing
#      the underlying edge, just flipping sign to non-wrap) also interlaces.
#      I.e. if W' = W - {e} (same G),
#        lambda_i(L_sig(G, W')) lies in [lambda_{i-1}(L_sig(G,W)),
#                                        lambda_i(L_sig(G,W))+2]
#      because rank-1 sign flip is a rank-2 difference (A_sig' = A_sig with
#      one edge flipped = 2*E_uv rank-2 perturbation).
#      Weaker statement that will hold: |lambda_i' - lambda_i| <= 2.
# ===========================================================================

def claim_b14_sign_flip_eig_stability():
    c = FuzzyClaim("B14", "|lambda_i(L_sig(G,W)) - lambda_i(L_sig(G,W-e))| <= 2",
                   "e is an edge, W contains e (flip to non-wrap)")
    for n, G, W in small_instances():
        for e in W:
            W2 = frozenset(W - {e})
            Lsig_W = laplacian_signed(G, W)
            Lsig_W2 = laplacian_signed(G, W2)
            ev1 = sorted(np.linalg.eigvalsh(Lsig_W))
            ev2 = sorted(np.linalg.eigvalsh(Lsig_W2))
            ok = all(abs(a - b) <= 2.0 + 1e-6 for a, b in zip(ev1, ev2))
            if not ok:
                diffs = [abs(a - b) for a, b in zip(ev1, ev2)]
                c.record(False, {**describe(G, W), "flipped_edge": list(e),
                                 "max_diff": max(diffs),
                                 "ev1": [float(x) for x in ev1],
                                 "ev2": [float(x) for x in ev2]})
            else:
                c.record(True)
    return c


# ===========================================================================
# B15  Multi-edge interlacing (generalizing R5 R17):
#      Removing k non-wrap edges gives interlacing of order k, i.e.
#      lambda_{i-k}(L_sig(G)) <= lambda_i(L_sig(G-E')) for every i and every
#      set E' of k non-wrap edges.
# ===========================================================================

def claim_b15_multi_edge_interlacing():
    c = FuzzyClaim("B15", "lambda_i(L_sig(G-E')) >= lambda_{i-k}(L_sig(G)) for k=|E'| non-wrap edges",
                   "E' a set of non-wrap edges")
    for n, G, W in small_instances():
        nonwrap = [e for e in edge_list(G) if e not in W]
        if len(nonwrap) < 2:
            continue
        # Test pairs (k=2) to bound runtime.
        for e1, e2 in itertools.combinations(nonwrap, 2):
            Ge = G.copy()
            Ge.remove_edge(*e1)
            Ge.remove_edge(*e2)
            ev_G = sorted(np.linalg.eigvalsh(laplacian_signed(G, W)))
            ev_Ge = sorted(np.linalg.eigvalsh(laplacian_signed(Ge, W)))
            k = 2
            ok = True
            for i in range(len(ev_Ge)):
                # lambda_i(G-E') >= lambda_{i-k}(G) with i-k truncated at 0 handled below.
                if i - k >= 0:
                    if ev_Ge[i] + 1e-6 < ev_G[i - k]:
                        ok = False
                        break
                # upper: lambda_i(G-E') <= lambda_{i+k}(G) when i+k < len(ev_G)
                if i + k < len(ev_G):
                    if ev_Ge[i] - 1e-6 > ev_G[i + k]:
                        ok = False
                        break
            if not ok:
                c.record(False, {**describe(G, W), "removed": [list(e1), list(e2)],
                                 "ev_G": [float(x) for x in ev_G],
                                 "ev_Ge": [float(x) for x in ev_Ge]})
            else:
                c.record(True)
    return c


# ===========================================================================
# B16  Spectral-gap lower bound: if G connected and (G,W) is unbalanced,
#      lambda_min(L_sig) >= 4 * (1/(n * diam(G)^2))?  Literature gives
#      lambda_min(L_sig) >= 1/(diam * n)-style bound for the frustration.
#      Too weak to test uniformly.  Instead test a cleaner bound:
#        lambda_min(L_sig) >= 0, with equality iff (G,W) has a balanced comp.
#      This is EXACTLY R5 R10; but add sharpening:
#        if unbalanced,  lambda_min(L_sig) >= 2 - 2 * cos(pi/(2n)).
#      Too optimistic.  Let's test the simpler positivity-on-unbalanced:
#        lambda_min(L_sig) > 0 iff beta(G,W) = 0 AND G connected.
#  (this cleanly extends R5 R10 to the connected-strict case.)
# ===========================================================================

def claim_b16_strict_positivity_of_lmin_sig():
    c = FuzzyClaim("B16", "connected G, beta=0 => lambda_min(L_sig) > 0",
                   "G connected, beta(G,W)=0")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        if beta(G, W) != 0:
            continue
        Lsig = laplacian_signed(G, W)
        lmin = min(np.linalg.eigvalsh(Lsig))
        ok = lmin > TOL
        if not ok:
            c.record(False, {**describe(G, W), "lmin_sig": float(lmin)})
        else:
            c.record(True)
    return c


# ===========================================================================
# B17  Frobenius-norm split:  ||L_mob||_F^2 = ||L_s||_F^2 + ||L_sig||_F^2.
#      Sharpening of R5 R19.  Follows from B7 via sum of squared eigs.
# ===========================================================================

def claim_b17_frob_split():
    c = FuzzyClaim("B17", "||L_mob||_F^2 = ||L_s||_F^2 + ||L_sig||_F^2",
                   "any G, any W")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        lhs = frob_sq(Lm)
        rhs = frob_sq(Ls) + frob_sq(Lsig)
        ok = abs(lhs - rhs) < 1e-6 * (1 + abs(rhs))
        if not ok:
            c.record(False, {**describe(G, W), "lhs": lhs, "rhs": rhs})
        else:
            c.record(True)
    return c


# ===========================================================================
# B18  Characteristic-polynomial factorisation:
#        p_{L_mob}(lambda) = p_{L_s}(lambda) * p_{L_sig}(lambda).
#      Sharpens R5 R14 (fibre-restriction rank).  If true, entire L_mob
#      spectral theory reduces to the two smaller polynomials.
# ===========================================================================

def claim_b18_charpoly_factorisation():
    c = FuzzyClaim("B18", "p_{L_mob} = p_{L_s} * p_{L_sig}",
                   "any G, any W -- polynomial identity")
    xs = [0.5, 1.3, 2.7, -1.1]
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        nn = Ls.shape[0]
        for x in xs:
            pm = float(np.linalg.det(x * np.eye(2 * nn) - Lm))
            ps = float(np.linalg.det(x * np.eye(nn) - Ls))
            psig = float(np.linalg.det(x * np.eye(nn) - Lsig))
            rhs = ps * psig
            scale = 1.0 + abs(pm) + abs(rhs)
            ok = abs(pm - rhs) < 1e-5 * scale
            if not ok:
                c.record(False, {**describe(G, W), "x": x,
                                 "pm": pm, "ps_times_psig": rhs})
            else:
                c.record(True)
    return c


# ===========================================================================
# B19  Second-eigenvalue comparison:
#        lambda_2(L_mob) = min(lambda_2(L_s), lambda_2(L_sig)) ???
#      Naive from B7.  BUT lambda_2 here is the SECOND-SMALLEST over the
#      merged multiset; need to subtract the multiplicity-of-zero counts.
#      Careful formulation: sort spec(L_mob); the 2nd smallest equals
#         min(nonzero-eigs of combined multiset).
#      Simpler cross-check: lambda_2(L_mob) = min(lambda_2(L_s),
#                                                  lambda_min_pos(L_sig)).
#  where lambda_min_pos is smallest positive eigenvalue.
#  Let's test: sort(L_mob)[kerL_mob-dim] == min of positive eigs of L_s
#  union L_sig.
# ===========================================================================

def claim_b19_smallest_positive_mob():
    c = FuzzyClaim("B19", "smallest-positive-eig(L_mob) = min(smallest-pos(L_s), smallest-pos(L_sig))",
                   "any G, any W, smallest positive = first eig > TOL")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        def smallest_pos(M):
            ev = np.linalg.eigvalsh(M)
            pos = [x for x in ev if x > TOL]
            return min(pos) if pos else math.inf
        lm_pos = smallest_pos(Lm)
        rhs = min(smallest_pos(Ls), smallest_pos(Lsig))
        if math.isinf(lm_pos) and math.isinf(rhs):
            c.record(True)
            continue
        if math.isinf(lm_pos) or math.isinf(rhs):
            c.record(False, {**describe(G, W), "lm_pos": lm_pos, "rhs": rhs})
            continue
        ok = abs(lm_pos - rhs) < 1e-5 * (1 + abs(rhs))
        if not ok:
            c.record(False, {**describe(G, W),
                             "lm_pos": float(lm_pos), "rhs": float(rhs)})
        else:
            c.record(True)
    return c


# ===========================================================================
# B20  Covering-graph trace: for each vertex u,
#        (L_mob)_{uu} = 2 * deg(u) (block I_2 on diag), so tr L_mob = 4m.
#      Claim:  tr L_mob = 2 * tr L_s = 2 * tr L_sig.
#      Trivially from R5 R18 + diag structure; added as a structural sanity.
# ===========================================================================

def claim_b20_tr_mob_equals_2x():
    c = FuzzyClaim("B20", "tr(L_mob) = 2 * tr(L_s) = 2 * tr(L_sig) = 4 * |E|",
                   "any G, any W")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        tm = float(np.trace(Lm))
        ts = float(np.trace(Ls))
        tsig = float(np.trace(Lsig))
        ok = (abs(tm - 2 * ts) < 1e-9
              and abs(tm - 2 * tsig) < 1e-9
              and abs(tm - 4 * G.number_of_edges()) < 1e-9)
        if not ok:
            c.record(False, {**describe(G, W),
                             "tm": tm, "ts": ts, "tsig": tsig,
                             "m": G.number_of_edges()})
        else:
            c.record(True)
    return c


# ===========================================================================
# B21  Sign-function trace: if L_sig is PSD and has exactly beta zero
#      eigenvalues, then rank(L_sig) = n - beta, so
#        tr(sign(L_sig)) = n - beta(G,W).
#  (sign(0) = 0, sign(x>0) = 1 in the PSD sense.)
# ===========================================================================

def claim_b21_tr_sign_lsig_rank():
    c = FuzzyClaim("B21", "tr(sign(L_sig)) = n - beta(G,W)",
                   "sign defined via eigenvalue sign; L_sig PSD so signs in {0,1}")
    for n, G, W in small_instances():
        Lsig = laplacian_signed(G, W)
        ev = np.linalg.eigvalsh(Lsig)
        signs = np.where(np.abs(ev) < TOL, 0.0, np.where(ev > 0, 1.0, -1.0))
        tr_sign = float(np.sum(signs))
        rhs = G.number_of_nodes() - beta(G, W)
        ok = abs(tr_sign - rhs) < 1e-6
        if not ok:
            c.record(False, {**describe(G, W),
                             "tr_sign": tr_sign, "rhs": rhs,
                             "ev": [float(x) for x in sorted(ev)]})
        else:
            c.record(True)
    return c


# ---------------------------------------------------------------------------
# n = 6 extension for claims scoring tau = 1 on small_instances
# ---------------------------------------------------------------------------

# To keep runtime tractable the n=6 extension is done for a subset of
# claims that we expect to push hardest (i.e. those that pass n=5 cleanly).
# We run the full claim-fn on the n=6 deterministic sample and aggregate.

def extend_n6(claim_fn):
    """Re-invoke claim_fn but monkey-patching small_instances to n6_sample."""
    import builtins
    orig = globals()["small_instances"]
    globals()["small_instances"] = lambda: n6_sample()
    try:
        c = claim_fn()
    finally:
        globals()["small_instances"] = orig
    # Re-label idx to indicate n=6 subrun
    c.idx = str(c.idx) + "+n6"
    return c


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

CLAIM_FNS = [
    claim_b1_higher_trace_split,
    claim_b2_mixed_s_sig,
    claim_b3_mixed_s_mob_lift,
    claim_b4_trace_power_monotone,
    claim_b5_lambda_max_order,
    claim_b6_lambda_max_mob_equals_max,
    claim_b7_spectrum_union,
    claim_b8_alg_conn_bounds_sig,
    claim_b9_kernel_dim_mob_count,
    claim_b10_op_norm_sig_le_s,
    claim_b11_ker_support_is_balanced_union,
    claim_b12_heat_trace_split,
    claim_b13_resolvent_split,
    claim_b14_sign_flip_eig_stability,
    claim_b15_multi_edge_interlacing,
    claim_b16_strict_positivity_of_lmin_sig,
    claim_b17_frob_split,
    claim_b18_charpoly_factorisation,
    claim_b19_smallest_positive_mob,
    claim_b20_tr_mob_equals_2x,
    claim_b21_tr_sign_lsig_rank,
]


def main(out_json):
    results = []
    print(f"Running {len(CLAIM_FNS)} beta-tile claims on n in {{3,4,5}} exhaustive...")
    for fn in CLAIM_FNS:
        print(f"  {fn.__name__} ...", flush=True)
        c = fn()
        print(f"    tau = {c.tau:.4f}  ({c.passed}/{c.tested})")
        results.append(c.to_dict())

    # n=6 extension on top-7 claims by tau (and non-trivial sample size)
    results_sorted = sorted(results, key=lambda r: (-r["tau"], -r["tested"]))
    top = [r for r in results_sorted if r["tau"] == 1.0 and r["tested"] >= 50][:10]
    print(f"\nExtending to n=6 sample on {len(top)} claims ...")
    for r in top:
        fn = next(f for f in CLAIM_FNS if f.__name__.endswith(r["idx"].lower())
                  or f.__name__.split("_")[1] == r["idx"].lower())
        c6 = extend_n6(fn)
        print(f"  {r['idx']}+n6 tau = {c6.tau:.4f}  ({c6.passed}/{c6.tested})")
        results.append(c6.to_dict())

    Path(out_json).write_text(json.dumps(results, indent=2, default=str))
    print(f"\nWrote {out_json}")
    print("\nRanked by tau:")
    for r in sorted(results, key=lambda r: (-r["tau"], str(r["idx"]))):
        print(f"  {r['idx']:>6}  tau={r['tau']:.4f}  ({r['passed']}/{r['tested']})  {r['name']}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).parent / "results_beta.json")
    main(out)
