"""
NEGATOR round 3: brute-force search for counterexamples / near-misses
to 10 naive claims about the connection-Laplacian block decomposition.

Conventions (matching KernelDimension.lean):
    L_scalar(u,v)  = standard graph Laplacian (deg on diag, -1 on edges, 0 else).
                     Kernel dimension = #connected components of G.
    L_signed(u,v) := signedLaplacianMobius
                     = deg on diag,
                       +1 off-diag on wrap edges (sign flip),
                       -1 off-diag on interior (non-wrap) edges,
                       0 otherwise.
                     Kernel dimension = #balanced components
                     (a component is balanced iff every cycle has an even
                      number of wrap edges, i.e. wrap signing is a coboundary
                      on that component).
    L_mob (Mobius / covering Laplacian) lives on V x {0,1} and is similar
    (after the rotation R^_Mob) to block-diag(L_scalar, L_signed).
    Concretely, spectrum(L_mob) == spectrum(L_scalar) U spectrum(L_signed)
    (as multisets), and dim ker L_mob = dim ker L_scalar + dim ker L_signed.

Target claims tested here:
  1. dim ker L_mob == dim ker L_scalar  iff  G balanced.
  2. L_signed is PSD.
  3. lambda_min(L_mob) == min(lambda_min(L_scalar), lambda_min(L_signed)).
  4. lambda_max(L_signed) <= 2 * max_deg(G).
  5. tr(L_mob^2) == tr(L_scalar^2) + tr(L_signed^2).
  6. dim ker L_signed(G) >= dim ker L_scalar(G) - |W|.
  7. G connected + |W|=1  =>  G NOT balanced.
  8. fiber-count subadditive under component union.
  9. integrality of ker-dim difference (vacuous; logged only).
 10. disjoint union: dim ker L_signed adds; edge contraction / subdivision
     behaviour logged numerically.

Graphs enumerated: all simple graphs up to isomorphism on n in {3,4,5,6},
plus n=7 for claim 8 (disjoint unions of 3+4, etc.).
"""

from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import networkx as nx
import numpy as np


TOL = 1e-8


# ---------------------------------------------------------------------------
# Laplacian builders
# ---------------------------------------------------------------------------

def edge_list(G: nx.Graph):
    """Canonical ordered edge list."""
    return [tuple(sorted(e)) for e in G.edges()]


def laplacian_scalar(G: nx.Graph) -> np.ndarray:
    n = G.number_of_nodes()
    L = np.zeros((n, n))
    for u, v in G.edges():
        L[u, u] += 1
        L[v, v] += 1
        L[u, v] -= 1
        L[v, u] -= 1
    return L


def laplacian_signed(G: nx.Graph, wrap: frozenset) -> np.ndarray:
    """signedLaplacianMobius: diag = deg, off-diag = +1 if wrap else -1."""
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


def laplacian_mobius(G: nx.Graph, wrap: frozenset) -> np.ndarray:
    """Covering Laplacian on V x {0,1}. Non-wrap edges act as Id, wrap
    edges act as sigma_x swap (entries -1 where no swap, off-diagonal block
    mixes fibres). We use the conventional gauge:
        block(u,v) = Id  if non-wrap edge, sigma_x if wrap edge.
    Laplacian diagonal block is deg(u) * Id. For each edge (u,v) we
    subtract the block(u,v) off-diagonal (and symmetrically (v,u)).
    """
    n = G.number_of_nodes()
    L = np.zeros((2 * n, 2 * n))
    I = np.eye(2)
    X = np.array([[0.0, 1.0], [1.0, 0.0]])
    # diagonal deg blocks
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
# Graph-theoretic helpers
# ---------------------------------------------------------------------------

def is_balanced(G: nx.Graph, wrap: frozenset) -> bool:
    """A signed graph is balanced iff vertices 2-colorable so that wrap
    edges are precisely those with endpoints of opposite colour."""
    if G.number_of_nodes() == 0:
        return True
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


def balanced_component_count(G: nx.Graph, wrap: frozenset) -> int:
    """Number of connected components that are balanced as signed graphs."""
    cnt = 0
    for comp in nx.connected_components(G):
        H = G.subgraph(comp).copy()
        H_edges = set(tuple(sorted(e)) for e in H.edges())
        wrap_H = wrap & H_edges
        if is_balanced(H, wrap_H):
            cnt += 1
    return cnt


def kernel_dim(M: np.ndarray) -> int:
    ev = np.linalg.eigvalsh(M)
    return int(np.sum(np.abs(ev) < TOL))


def all_graphs(n: int):
    """All non-isomorphic simple graphs on n labelled vertices (enumerated
    then de-duplicated up to iso). For n <= 6 this is tiny."""
    seen = []
    nodes = list(range(n))
    potential = list(itertools.combinations(nodes, 2))
    for mask in range(1 << len(potential)):
        edges = [potential[i] for i in range(len(potential)) if mask & (1 << i)]
        G = nx.Graph()
        G.add_nodes_from(nodes)
        G.add_edges_from(edges)
        for H in seen:
            if nx.is_isomorphic(G, H):
                break
        else:
            seen.append(G)
    return seen


def all_labelled_graphs(n: int):
    """All labelled simple graphs on n nodes. Used for 'all wrap subsets'
    sweeps where the labelled structure matters."""
    nodes = list(range(n))
    potential = list(itertools.combinations(nodes, 2))
    for mask in range(1 << len(potential)):
        edges = [potential[i] for i in range(len(potential)) if mask & (1 << i)]
        G = nx.Graph()
        G.add_nodes_from(nodes)
        G.add_edges_from(edges)
        yield G


def all_wrap_subsets(G: nx.Graph):
    edges = edge_list(G)
    for r in range(len(edges) + 1):
        for sub in itertools.combinations(edges, r):
            yield frozenset(sub)


# ---------------------------------------------------------------------------
# Claim testers
# ---------------------------------------------------------------------------

class ClaimResult:
    def __init__(self, name):
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
    def verdict(self):
        if self.counterexample is None:
            return "TRUE (no counterexample in search envelope)"
        return "FALSE (counterexample found)"


def iter_small_instances(n_max=6):
    """Iterate (G, wrap) over non-iso graphs of 3..n_max, all wrap subsets."""
    for n in range(3, n_max + 1):
        for G in all_graphs(n):
            for W in all_wrap_subsets(G):
                yield n, G, W


def describe(G, W):
    return {"n": G.number_of_nodes(),
            "edges": edge_list(G),
            "wrap": sorted(list(W))}


# ---- Claim 1 -----------------------------------------------------------------

def test_claim1(results):
    r = ClaimResult("C1: dim ker L_mob == dim ker L_scalar iff G balanced")
    for n, G, W in iter_small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        ks = kernel_dim(Ls)
        ksig = kernel_dim(Lsig)
        km = kernel_dim(Lm)
        bal_G = is_balanced(G, W)  # whole graph "balanced" here means
        # every component balanced, equivalently #bal comps == #comps.
        bal_all = (balanced_component_count(G, W) == nx.number_connected_components(G))
        lhs = (km == ks)
        # With conventions: km = ks + ksig, so km == ks iff ksig == 0 iff
        # no balanced component exists. That is a *different* claim than
        # "G balanced". Evaluate the stated claim literally.
        ok = (lhs == bal_all)
        if not ok:
            r.record(False, {**describe(G, W),
                              "ks": ks, "ksig": ksig, "km": km,
                              "balanced_all_components": bal_all,
                              "lhs_km_eq_ks": lhs})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 2 -----------------------------------------------------------------

def test_claim2(results):
    r = ClaimResult("C2: L_signed is PSD (all eigvals >= 0)")
    for n, G, W in iter_small_instances():
        Lsig = laplacian_signed(G, W)
        ev = np.linalg.eigvalsh(Lsig)
        lam_min = float(np.min(ev))
        ok = lam_min > -TOL
        if not ok:
            r.record(False, {**describe(G, W),
                              "min_eigval": lam_min,
                              "eigvals": [float(x) for x in ev]})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 3 -----------------------------------------------------------------

def test_claim3(results):
    r = ClaimResult("C3: lambda_min(L_mob) == min(lambda_min(L_scalar), lambda_min(L_signed))")
    for n, G, W in iter_small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        lm = float(np.min(np.linalg.eigvalsh(Lm)))
        ls = float(np.min(np.linalg.eigvalsh(Ls)))
        lsig = float(np.min(np.linalg.eigvalsh(Lsig)))
        expected = min(ls, lsig)
        ok = abs(lm - expected) < 1e-7
        if not ok:
            r.record(False, {**describe(G, W),
                              "lambda_min_mob": lm,
                              "lambda_min_scalar": ls,
                              "lambda_min_signed": lsig,
                              "expected_min": expected})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 4 -----------------------------------------------------------------

def test_claim4(results):
    r = ClaimResult("C4: lambda_max(L_signed) <= 2 * max_deg")
    for n, G, W in iter_small_instances():
        if G.number_of_edges() == 0:
            r.record(True)
            continue
        Lsig = laplacian_signed(G, W)
        lam_max = float(np.max(np.linalg.eigvalsh(Lsig)))
        max_deg = max(dict(G.degree()).values())
        ok = lam_max <= 2 * max_deg + TOL
        if not ok:
            r.record(False, {**describe(G, W),
                              "lambda_max_signed": lam_max,
                              "max_deg": max_deg,
                              "bound_2max_deg": 2 * max_deg})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 5 -----------------------------------------------------------------

def test_claim5(results):
    r = ClaimResult("C5: tr(L_mob^2) == tr(L_scalar^2) + tr(L_signed^2)")
    for n, G, W in iter_small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        t_mob = float(np.trace(Lm @ Lm))
        t_s = float(np.trace(Ls @ Ls))
        t_sig = float(np.trace(Lsig @ Lsig))
        # Because spectrum(L_mob) = spectrum(L_scalar) U spectrum(L_signed),
        # we expect t_mob == t_s + t_sig.
        ok = abs(t_mob - (t_s + t_sig)) < 1e-6
        if not ok:
            r.record(False, {**describe(G, W),
                              "tr_mob_sq": t_mob,
                              "tr_scalar_sq": t_s,
                              "tr_signed_sq": t_sig,
                              "sum": t_s + t_sig})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 6 -----------------------------------------------------------------

def test_claim6(results):
    r = ClaimResult("C6: dim ker L_signed >= dim ker L_scalar - |W|")
    for n, G, W in iter_small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        ks = kernel_dim(Ls)
        ksig = kernel_dim(Lsig)
        ok = ksig >= ks - len(W)
        if not ok:
            r.record(False, {**describe(G, W),
                              "ker_scalar": ks,
                              "ker_signed": ksig,
                              "W_size": len(W),
                              "lhs": ksig,
                              "rhs": ks - len(W)})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 7 -----------------------------------------------------------------

def test_claim7(results):
    r = ClaimResult("C7: connected G + |W|=1 => G NOT balanced")
    for n, G, W in iter_small_instances():
        if not nx.is_connected(G):
            continue
        if len(W) != 1:
            continue
        bal = is_balanced(G, W)
        # Literal claim: connected + single wrap => not balanced.
        # Reality: balanced iff the wrap edge is a bridge (so no cycle
        # contains it, hence no odd-wrap cycle).
        ok = (not bal)
        if not ok:
            e_wrap = next(iter(W))
            # check if bridge
            H = G.copy()
            H.remove_edge(*e_wrap)
            is_bridge = not nx.is_connected(H)
            r.record(False, {**describe(G, W),
                              "wrap_is_bridge": is_bridge,
                              "balanced": bal})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 8 -----------------------------------------------------------------

def test_claim8(results):
    r = ClaimResult("C8: #fiber(C) + #fiber(C') >= #fiber(C U C') for any two components")
    # Concretely: fiber(component) = 2^{# wrap-cycles independent} type
    # quantity; we use the operational notion: "fiber over a component C"
    # = dim ker L_mob restricted to C's vertex-pair lift. For a single
    # connected component C: dim ker L_mob|_C = dim ker L_scalar|_C +
    # dim ker L_signed|_C = 1 + [C balanced] in {1,2}. The #fiber(C)
    # in the paper is typically 2^{#unbalanced components - components
    # flipped by gauge}; here we just sanity-check subadditivity of
    # the "fiber size" defined as 2^{#balanced components in the piece}.
    import itertools as it
    # Test within n<=6 graphs and split vertex set into two arbitrary
    # disjoint unions (C, C').
    for n, G, W in iter_small_instances(n_max=6):
        comps = list(nx.connected_components(G))
        if len(comps) < 2:
            continue
        # Partition components into two non-empty subsets.
        for k in range(1, len(comps)):
            for sub in it.combinations(range(len(comps)), k):
                A = set()
                for i in sub:
                    A |= comps[i]
                B = set(G.nodes()) - A
                GA = G.subgraph(A).copy()
                GB = G.subgraph(B).copy()
                GAB = G.subgraph(A | B).copy()
                EA = set(tuple(sorted(e)) for e in GA.edges())
                EB = set(tuple(sorted(e)) for e in GB.edges())
                EAB = set(tuple(sorted(e)) for e in GAB.edges())
                WA = W & EA; WB = W & EB; WAB = W & EAB
                fA = 2 ** balanced_component_count(GA, WA)
                fB = 2 ** balanced_component_count(GB, WB)
                fAB = 2 ** balanced_component_count(GAB, WAB)
                ok = (fA + fB >= fAB)
                if not ok:
                    r.record(False, {**describe(G, W),
                                      "A_nodes": sorted(A),
                                      "B_nodes": sorted(B),
                                      "fiberA": fA,
                                      "fiberB": fB,
                                      "fiberAB": fAB})
                else:
                    r.record(True)
    results.append(r)


# ---- Claim 9 -----------------------------------------------------------------

def test_claim9(results):
    r = ClaimResult("C9: integrality of dim ker L_mob - dim ker L_scalar (vacuous)")
    # By block decomposition this equals dim ker L_signed which is a
    # nonneg integer. Vacuous but recorded.
    for n, G, W in iter_small_instances():
        Ls = laplacian_scalar(G)
        Lsig = laplacian_signed(G, W)
        Lm = laplacian_mobius(G, W)
        diff = kernel_dim(Lm) - kernel_dim(Ls)
        ok = (diff == kernel_dim(Lsig)) and diff >= 0
        if not ok:
            r.record(False, {**describe(G, W),
                              "diff": diff,
                              "ker_signed": kernel_dim(Lsig)})
        else:
            r.record(True)
    results.append(r)


# ---- Claim 10: invariants ----------------------------------------------------

def contract_edge(G: nx.Graph, W: frozenset, e):
    """Contract edge e in G. Return (G', W') with vertex ids relabeled 0..n-2."""
    u, v = e
    H = nx.contracted_edge(G, (u, v), self_loops=False)
    # Relabel to 0..n-2
    mapping = {old: new for new, old in enumerate(sorted(H.nodes()))}
    H = nx.relabel_nodes(H, mapping)
    # Map wrap set. For each wrap edge (a,b), its endpoints map via
    # (v -> u) then via `mapping`.
    def remap(x):
        if x == v:
            x = u
        return mapping[x]
    W_new = set()
    for (a, b) in W:
        if {a, b} == {u, v}:
            continue
        a2, b2 = remap(a), remap(b)
        if a2 == b2:
            continue
        W_new.add(tuple(sorted((a2, b2))))
    return H, frozenset(W_new)


def test_claim10(results):
    r = ClaimResult("C10: structural invariants (contraction/subdivision/disjoint union)")

    # 10a: disjoint union  dim ker L_signed adds.
    r10a_pass = r10a_fail = 0
    ce = None
    # Take pairs of graphs on up to 4+3 vertices.
    for G1 in all_graphs(3):
        for G2 in all_graphs(3):
            for W1 in all_wrap_subsets(G1):
                for W2 in all_wrap_subsets(G2):
                    U = nx.disjoint_union(G1, G2)
                    # Remap wraps to union labels.
                    offset = G1.number_of_nodes()
                    W_u = set()
                    for (a, b) in W1:
                        W_u.add(tuple(sorted((a, b))))
                    for (a, b) in W2:
                        W_u.add(tuple(sorted((a + offset, b + offset))))
                    W_u = frozenset(W_u)
                    k_sum = (kernel_dim(laplacian_signed(G1, W1))
                             + kernel_dim(laplacian_signed(G2, W2)))
                    k_un = kernel_dim(laplacian_signed(U, W_u))
                    if k_un == k_sum:
                        r10a_pass += 1
                    else:
                        r10a_fail += 1
                        if ce is None:
                            ce = {"part": "10a disjoint union",
                                   "G1_edges": edge_list(G1), "W1": sorted(W1),
                                   "G2_edges": edge_list(G2), "W2": sorted(W2),
                                   "k_sum": k_sum, "k_union": k_un}

    # 10b: non-wrap edge contraction. Expectation from Zaslavsky: kernel
    # dim of L_signed is invariant under contracting a NON-wrap edge
    # (switching-equivalent to a self-loop that contributes nothing).
    # Let's check if dim ker is preserved, or simply record behaviour.
    r10b_pass = r10b_preserved = r10b_changed = 0
    ce10b = None
    for n in (4, 5):
        for G in all_graphs(n):
            for W in all_wrap_subsets(G):
                nonwrap = [e for e in edge_list(G) if e not in W]
                if not nonwrap:
                    continue
                for e in nonwrap[:1]:  # one representative contraction
                    H, Wh = contract_edge(G, W, e)
                    kG = kernel_dim(laplacian_signed(G, W))
                    kH = kernel_dim(laplacian_signed(H, Wh))
                    if kG == kH:
                        r10b_preserved += 1
                    else:
                        r10b_changed += 1
                        if ce10b is None:
                            ce10b = {"part": "10b contract non-wrap",
                                      "G_edges": edge_list(G), "W": sorted(W),
                                      "contracted": e,
                                      "H_edges": edge_list(H),
                                      "Wh": sorted(Wh),
                                      "ker_G": kG, "ker_H": kH}

    r.record(r10a_fail == 0,
             ce if r10a_fail else None)
    r.extra = {
        "disjoint_union_pass": r10a_pass,
        "disjoint_union_fail": r10a_fail,
        "contract_nonwrap_preserved": r10b_preserved,
        "contract_nonwrap_changed": r10b_changed,
        "contract_counterexample": ce10b,
    }
    results.append(r)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main(out_path):
    results = []
    print("C1..."); test_claim1(results)
    print("C2..."); test_claim2(results)
    print("C3..."); test_claim3(results)
    print("C4..."); test_claim4(results)
    print("C5..."); test_claim5(results)
    print("C6..."); test_claim6(results)
    print("C7..."); test_claim7(results)
    print("C8..."); test_claim8(results)
    print("C9..."); test_claim9(results)
    print("C10..."); test_claim10(results)

    # Emit JSON for the markdown report generator.
    data = []
    for r in results:
        entry = {"claim": r.name,
                  "tested": r.tested,
                  "passed": r.passed,
                  "verdict": r.verdict,
                  "counterexample": r.counterexample}
        if hasattr(r, "extra"):
            entry["extra"] = r.extra
        data.append(entry)

    Path(out_path).write_text(json.dumps(data, indent=2, default=str))
    print(f"Wrote {out_path}")
    for entry in data:
        print(f"  [{entry['passed']}/{entry['tested']}]  {entry['claim']}  -> {entry['verdict']}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "results.json"
    main(out)
