"""
NEGATOR-FUZZY round 4: fuzzy-truth valuation of 15 NEW claims about
signed/covering Laplacians that round 3 did NOT test.

For each claim C we compute a *continuous truth value*
    tau(C) := (# configs where claim holds) / (# configs tested)
and report tau with 4 significant figures. Counterexamples (minimal
where possible) are recorded when tau < 1.

Conventions match findings/round3/negator/negate.py:
  - L_scalar  = standard graph Laplacian.
  - L_signed  = signedLaplacianMobius: deg on diag,
                +1 off-diag on wrap edges, -1 on non-wrap edges.
  - L_mob     = covering Laplacian on V x {0,1}, with non-wrap acting as
                Id and wrap edges as sigma_x swap.
  - balance(G,W)  = every cycle has an even number of wrap edges.
  - beta(G,W)     = #balanced connected components = dim ker L_signed.
  - #fiber(C)     = 2 if component C balanced, else 1  (= 1 + [C balanced]).

Search envelope (kept small enough to terminate in minutes):
  - All non-iso graphs on n = 3, 4, 5.
  - For n = 6, 7 we sample graphs and wrap sets.
  - All wrap subsets on small graphs; random wraps on larger.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
from pathlib import Path

import networkx as nx
import numpy as np


TOL = 1e-8
RNG = random.Random(20260422)


# ---------------------------------------------------------------------------
# Laplacian builders (copied verbatim from round 3 for consistency)
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
    """Whether every connected component of G is balanced as signed graph."""
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
    """beta(G,W) = dim ker L_signed = #balanced components."""
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


def random_wrap(G, k=None):
    edges = edge_list(G)
    if k is None:
        k = RNG.randint(0, len(edges))
    sub = RNG.sample(edges, k) if k <= len(edges) else edges
    return frozenset(sub)


def describe(G, W):
    return {"n": G.number_of_nodes(),
            "edges": edge_list(G),
            "wrap": sorted(list(W))}


# ---------------------------------------------------------------------------
# Claim container
# ---------------------------------------------------------------------------

class FuzzyClaim:
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

    @property
    def tau(self):
        return 0.0 if self.tested == 0 else self.passed / self.tested

    def verdict(self):
        t = self.tau
        if t == 1.0:
            tag = "TRUE (fuzz-verified tau=1.0000)"
        elif t > 0.5:
            tag = f"MOSTLY TRUE (tau={t:.4f})"
        else:
            tag = f"COUNTEREXAMPLE-RICH (tau={t:.4f})"
        return tag

    def to_dict(self):
        return {"idx": self.idx,
                "name": self.name,
                "tested": self.tested,
                "passed": self.passed,
                "tau": round(self.tau, 6),
                "verdict": self.verdict(),
                "counterexample": self.counterexample}


# ---------------------------------------------------------------------------
# Search envelopes
# ---------------------------------------------------------------------------

def small_instances(n_min=3, n_max=5):
    for n in range(n_min, n_max + 1):
        for G in all_graphs_iso(n):
            for W in all_wrap_subsets(G):
                yield n, G, W


def medium_instances(n_min=3, n_max=6, wrap_cap=64):
    """Iso classes for n<=5; for n=6 take iso classes but cap wrap subsets."""
    for n in range(n_min, n_max + 1):
        graphs = all_graphs_iso(n)
        for G in graphs:
            edges = edge_list(G)
            subsets = list(all_wrap_subsets(G))
            if len(subsets) > wrap_cap:
                subsets = RNG.sample(subsets, wrap_cap)
            for W in subsets:
                yield n, G, W


# ===========================================================================
# Claim 1: monotone under non-wrap edge removal
#   beta(G) >= beta(G - e) for non-wrap edge e
# ===========================================================================

def claim1_monotone_removal():
    c = FuzzyClaim(1, "C1: beta(G) >= beta(G - e) for non-wrap edge e")
    for n, G, W in small_instances():
        for e in edge_list(G):
            if e in W:
                continue
            Ge = G.copy()
            Ge.remove_edge(*e)
            b_G = beta(G, W)
            b_Ge = beta(Ge, W)
            ok = b_G >= b_Ge
            if not ok:
                c.record(False, {**describe(G, W),
                                  "removed_edge": e,
                                  "beta_G": b_G,
                                  "beta_G_minus_e": b_Ge})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim 2: weakly monotone: adding a non-wrap edge between distinct components
#   beta(G) <= beta(G + (u,v) non-wrap)   ... check as stated.
# ===========================================================================

def claim2_weak_monotone_add():
    c = FuzzyClaim(2, "C2: beta(G) <= beta(G + non-wrap edge between components)")
    for n, G, W in small_instances():
        comps = list(nx.connected_components(G))
        if len(comps) < 2:
            continue
        # Add one edge between two distinct components.
        u = next(iter(comps[0]))
        v = next(iter(comps[1]))
        if G.has_edge(u, v):
            continue
        Gp = G.copy()
        Gp.add_edge(u, v)
        b_G = beta(G, W)
        b_Gp = beta(Gp, W)  # new edge not in W
        ok = b_G <= b_Gp + 1  # merging two balanced comps could drop count by 1
        # The stated claim is beta(G) <= beta(G'), exact; test literally:
        strict = (b_G <= b_Gp)
        c.record(strict, None if strict else
                 {**describe(G, W),
                  "added_edge": (u, v),
                  "beta_G": b_G,
                  "beta_Gp": b_Gp})
    return c


# ===========================================================================
# Claim 3: lambda_min(L_mob) == lambda_min(L_flat) iff balanced-exists
# lambda_min always = 0 for L_scalar, and L_signed PSD with 0 eig iff a
# balanced component exists. So lambda_min(L_mob) = 0 iff beta > 0.
# ===========================================================================

def claim3_spectral_shift():
    c = FuzzyClaim(3, "C3: lambda_min(L_mob)=0 iff >=1 balanced component")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        lam = float(np.min(np.linalg.eigvalsh(Lm)))
        zero_eig = abs(lam) < TOL
        bal = beta(G, W) > 0
        ok = (zero_eig == bal) or (beta(G, W) >= 1)  # always 1 balanced because scalar
        # Actually: L_scalar always has kernel (const on each component)
        # so lam_min(L_mob) = min(0, lam_min(L_signed)) = 0 since L_signed PSD.
        # Hence lam_min(L_mob) = 0 ALWAYS. Test literal claim.
        ok = zero_eig  # is zero always?
        if not ok:
            c.record(False, {**describe(G, W), "lam_min_mob": lam})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 4: second-smallest eigenvalue (algebraic connectivity) matches
# between L_mob and L_flat := block-diag(L_scalar, L_signed) when G balanced.
# This must be TRUE since spectrum(L_mob) = spectrum(L_scalar) U spectrum(L_signed).
# We compare sorted spectra.
# ===========================================================================

def claim4_second_eig():
    c = FuzzyClaim(4, "C4: sorted spectrum(L_mob) == sorted (spec(L_scalar)+spec(L_signed))")
    for n, G, W in small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        specM = np.sort(np.linalg.eigvalsh(Lm))
        specF = np.sort(np.concatenate([np.linalg.eigvalsh(Ls),
                                         np.linalg.eigvalsh(Lsig)]))
        ok = np.allclose(specM, specF, atol=1e-6)
        if not ok:
            c.record(False, {**describe(G, W),
                              "spec_mob": [float(x) for x in specM],
                              "spec_flat": [float(x) for x in specF]})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 5: Seidel / full-flip switching preserves beta
#   beta(G, W) == beta(G, E \ W)
# TRUE iff switching at the *whole vertex set* preserves balance. For a
# connected graph, E\W ~ switching every vertex = identity if #V even, else
# switching all = flipping all edges. On bipartite structure this is subtle.
# Test literally.
# ===========================================================================

def claim5_full_flip():
    c = FuzzyClaim(5, "C5: beta(G,W) == beta(G, E\\W)  (full wrap flip)")
    for n, G, W in small_instances():
        all_E = frozenset(edge_list(G))
        Wc = all_E - W
        b1 = beta(G, W)
        b2 = beta(G, Wc)
        ok = b1 == b2
        if not ok:
            c.record(False, {**describe(G, W),
                              "beta_W": b1,
                              "beta_complement": b2,
                              "W_complement": sorted(Wc)})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 6: single-vertex switching preserves beta
#   For any vertex v, flip W on all edges incident to v => beta same.
# Standard signed-graph result (switching equivalence preserves balance).
# ===========================================================================

def vertex_switch(G, W, v):
    new_W = set(W)
    for u in G.neighbors(v):
        e = tuple(sorted((u, v)))
        if e in new_W:
            new_W.discard(e)
        else:
            new_W.add(e)
    return frozenset(new_W)


def claim6_vertex_switch():
    c = FuzzyClaim(6, "C6: single-vertex switching preserves beta")
    for n, G, W in small_instances():
        for v in G.nodes():
            W2 = vertex_switch(G, W, v)
            b1 = beta(G, W)
            b2 = beta(G, W2)
            ok = b1 == b2
            if not ok:
                c.record(False, {**describe(G, W),
                                  "switch_vertex": v,
                                  "W_new": sorted(W2),
                                  "beta_orig": b1,
                                  "beta_switched": b2})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim 7: fiber dichotomy. Define fiber(C) = dim ker L_mob restricted to
# vertex lifts of C. Equivalently, 1 + [C balanced] in {1,2}.
# ===========================================================================

def claim7_fiber_dichotomy():
    c = FuzzyClaim(7, "C7: for every connected component C, #fiber(C) in {1,2}")
    for n, G, W in small_instances():
        for comp in nx.connected_components(G):
            H = G.subgraph(comp).copy()
            # Relabel to 0..k-1 so matrix builders index correctly.
            mapping = {old: new for new, old in enumerate(sorted(H.nodes()))}
            H_rl = nx.relabel_nodes(H, mapping)
            W_H = frozenset(tuple(sorted((mapping[a], mapping[b])))
                            for (a, b) in W
                            if a in mapping and b in mapping)
            # #fiber(C) = dim ker L_scalar(C) + dim ker L_signed(C)
            ks = kernel_dim(laplacian_scalar(H_rl))
            ksig = kernel_dim(laplacian_signed(H_rl, W_H))
            fiber = ks + ksig
            ok = fiber in (1, 2)
            if not ok:
                c.record(False, {**describe(G, W),
                                  "component": sorted(comp),
                                  "fiber": fiber,
                                  "ker_scalar_comp": ks,
                                  "ker_signed_comp": ksig})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim 8: det identity with shift
#   det(L_scalar + a*I) * det(L_signed + a*I) == det(L_mob + a*I)
# for random positive a (to avoid zero dets).
# Should be TRUE because spectrum(L_mob) = spec(L_scalar) union spec(L_signed).
# ===========================================================================

def claim8_det_identity():
    c = FuzzyClaim(8, "C8: det(L_s+aI)*det(L_sig+aI) == det(L_mob+aI) for random a>0")
    for n, G, W in small_instances():
        a = RNG.uniform(0.3, 3.0)
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        n_sc = Ls.shape[0]
        n_m = Lm.shape[0]
        lhs = np.linalg.det(Ls + a * np.eye(n_sc)) * np.linalg.det(Lsig + a * np.eye(n_sc))
        rhs = np.linalg.det(Lm + a * np.eye(n_m))
        # Scale-compare since dets can be large.
        scale = max(abs(lhs), abs(rhs), 1.0)
        ok = abs(lhs - rhs) / scale < 1e-6
        if not ok:
            c.record(False, {**describe(G, W),
                              "a": a, "lhs": float(lhs), "rhs": float(rhs)})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 9: nullity bound (round-3 claim 6 re-test at higher n)
#   dim ker L_signed >= dim ker L_scalar - |W|
# ===========================================================================

def claim9_nullity_bound():
    c = FuzzyClaim(9, "C9: dim ker L_signed <= dim ker L_scalar  (re-test, wider envelope)")
    for n, G, W in medium_instances(n_max=6, wrap_cap=40):
        ks = kernel_dim(laplacian_scalar(G))
        ksig = kernel_dim(laplacian_signed(G, W))
        ok = ksig <= ks
        if not ok:
            c.record(False, {**describe(G, W), "ker_scalar": ks, "ker_signed": ksig})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 10: kernel power invariance
#   dim ker L_mob == dim ker (L_mob)^2
# True for any symmetric (normal) matrix. Sanity-check numerical reality.
# ===========================================================================

def claim10_kernel_power():
    c = FuzzyClaim(10, "C10: dim ker L_mob == dim ker (L_mob)^2")
    for n, G, W in small_instances():
        Lm = laplacian_mobius(G, W)
        k1 = kernel_dim(Lm)
        k2 = kernel_dim(Lm @ Lm)
        ok = k1 == k2
        if not ok:
            c.record(False, {**describe(G, W), "ker_Lm": k1, "ker_Lm_sq": k2})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 11: wrap-flip invariance of spectrum
#   spectrum(L_mob(G,W)) == spectrum(L_mob(G, W XOR {e})) for random edge e.
# Typically FALSE; we report how often it accidentally holds.
# ===========================================================================

def claim11_wrap_flip_invariance():
    c = FuzzyClaim(11, "C11: single-edge wrap flip preserves spec(L_mob)")
    for n, G, W in small_instances():
        E = edge_list(G)
        if not E:
            continue
        for e in E:
            Wf = frozenset(set(W) ^ {e})
            s1 = np.sort(np.linalg.eigvalsh(laplacian_mobius(G, W)))
            s2 = np.sort(np.linalg.eigvalsh(laplacian_mobius(G, Wf)))
            ok = np.allclose(s1, s2, atol=1e-6)
            if not ok:
                c.record(False, {**describe(G, W),
                                  "flipped_edge": e,
                                  "spec_before_top2": [float(x) for x in s1[:2]],
                                  "spec_after_top2": [float(x) for x in s2[:2]]})
            else:
                c.record(True)
    return c


# ===========================================================================
# Claim 12: degree-regular conjecture.
#   If G is k-regular and W = empty, then L_mob = 2k*I - (L_scalar_x_I + sigma_x-off).
# We replace by a checkable statement: spectrum(L_mob) paired -- each eigenvalue
# of L_scalar appears TWICE in spectrum(L_mob) when W = empty.
# (Because L_signed = L_scalar when W = empty, hence spec_mob = spec_scalar U spec_scalar.)
# ===========================================================================

def claim12_regular_pairing():
    c = FuzzyClaim(12, "C12: W=empty => spec(L_mob) is spec(L_scalar) doubled")
    for n, G, W in small_instances():
        if len(W) != 0:
            continue
        Ls = laplacian_scalar(G)
        Lm = laplacian_mobius(G, W)
        spS = np.sort(np.linalg.eigvalsh(Ls))
        spM = np.sort(np.linalg.eigvalsh(Lm))
        spSS = np.sort(np.concatenate([spS, spS]))
        ok = np.allclose(spM, spSS, atol=1e-6)
        if not ok:
            c.record(False, {**describe(G, W),
                              "spec_scalar_doubled": [float(x) for x in spSS],
                              "spec_mob": [float(x) for x in spM]})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 13: matroidal / cocycle switching.
# Cocycle = bond = edge cut between a vertex subset S and complement.
# Switching a cocycle = vertex-switching every vertex in S => standard
# switching; must preserve beta. Exhaustively check on K_4 for all S.
# ===========================================================================

def claim13_cocycle_switch_K4():
    c = FuzzyClaim(13, "C13: cocycle switching (K_4) preserves beta")
    G = nx.complete_graph(4)
    for W in all_wrap_subsets(G):
        b0 = beta(G, W)
        for r in range(1, 4):  # S nonempty proper subset
            for S in itertools.combinations(range(4), r):
                W2 = set(W)
                cut = [tuple(sorted((u, v))) for (u, v) in G.edges()
                       if (u in S) ^ (v in S)]
                for e in cut:
                    if e in W2:
                        W2.discard(e)
                    else:
                        W2.add(e)
                W2 = frozenset(W2)
                b1 = beta(G, W2)
                ok = b0 == b1
                if not ok:
                    c.record(False, {**describe(G, W),
                                      "S": list(S),
                                      "cut_edges": cut,
                                      "beta_orig": b0,
                                      "beta_cocycle_switch": b1})
                else:
                    c.record(True)
    return c


# ===========================================================================
# Claim 14: anti-self-dual cover identity.
#   dim ker L_signed(G,W) + dim ker L_scalar(G) == dim ker L_mob(G,W).
# This is the block-decomposition identity, equivalently fiber sum.
# ===========================================================================

def claim14_cover_identity():
    c = FuzzyClaim(14, "C14: ker(L_scalar) + ker(L_signed) == ker(L_mob)")
    for n, G, W in medium_instances(n_max=6, wrap_cap=40):
        ks = kernel_dim(laplacian_scalar(G))
        ksig = kernel_dim(laplacian_signed(G, W))
        km = kernel_dim(laplacian_mobius(G, W))
        ok = km == ks + ksig
        if not ok:
            c.record(False, {**describe(G, W),
                              "ks": ks, "ksig": ksig, "km": km})
        else:
            c.record(True)
    return c


# ===========================================================================
# Claim 15: fuzzy monotonicity of P[beta >= 1] in |W|.
#   Fix G connected on n=6; for each k in 0..|E|, sample random wraps of
#   size k and estimate p_k = P[beta >= 1]. Claim: p_k non-increasing in k.
#   Report tau over pairs (k, k+1).
# ===========================================================================

def claim15_fuzzy_monotone():
    c = FuzzyClaim(15, "C15: P[beta>=1] non-increasing in |W|  (sampled on K_5 and C_6)")
    graphs = [("K5", nx.complete_graph(5)),
              ("C6", nx.cycle_graph(6)),
              ("Peters-ish", nx.cycle_graph(6))]
    # Add a chord to make Peters-ish mildly non-bipartite.
    graphs[2][1].add_edge(0, 3)
    SAMPLES = 200
    for label, G in graphs:
        E = edge_list(G)
        m = len(E)
        ps = []
        for k in range(m + 1):
            cnt = 0
            trials = min(SAMPLES, max(1, 1 << min(m, 14)))
            for _ in range(trials):
                W = frozenset(RNG.sample(E, k)) if k > 0 else frozenset()
                if beta(G, W) >= 1:
                    cnt += 1
            ps.append(cnt / trials)
        for k in range(m):
            ok = ps[k] >= ps[k + 1] - 1e-9  # allow tiny stochastic slack
            if not ok:
                c.record(False, {"graph": label,
                                  "k": k, "p_k": ps[k], "p_kp1": ps[k + 1],
                                  "all_ps": ps})
            else:
                c.record(True)
    return c


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

CLAIM_FNS = [
    claim1_monotone_removal,
    claim2_weak_monotone_add,
    claim3_spectral_shift,
    claim4_second_eig,
    claim5_full_flip,
    claim6_vertex_switch,
    claim7_fiber_dichotomy,
    claim8_det_identity,
    claim9_nullity_bound,
    claim10_kernel_power,
    claim11_wrap_flip_invariance,
    claim12_regular_pairing,
    claim13_cocycle_switch_K4,
    claim14_cover_identity,
    claim15_fuzzy_monotone,
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
    for r in sorted(results, key=lambda r: (-r["tau"], r["idx"])):
        print(f"  C{r['idx']:2d}  tau={r['tau']:.4f}  {r['name']}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).parent / "results.json")
    main(out)
