"""Extend fuzzing to n=6 for R6-R22 top candidates."""
from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import networkx as nx
import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
from fuzz_r5 import (
    FuzzyClaim, laplacian_scalar, laplacian_signed, laplacian_mobius,
    beta, balanced_component_count, is_balanced_component, kernel_dim,
    edge_list, all_graphs_iso, all_wrap_subsets, random_wrap, relabel,
    describe, bridges, TOL
)

RNG = random.Random(20260423)


def sample_n6(n_graphs=20, wraps_per_graph=20):
    """Sample n=6 graphs and wrap sets."""
    all_G = all_graphs_iso(6)
    RNG.shuffle(all_G)
    for G in all_G[:n_graphs]:
        edges = edge_list(G)
        for _ in range(wraps_per_graph):
            k = RNG.randint(0, len(edges))
            W = frozenset(RNG.sample(edges, k))
            yield 6, G, W


def check_claim(name, test_fn):
    """Test a predicate on n=6 samples."""
    c = FuzzyClaim(name, name)
    for n, G, W in sample_n6():
        ok, ce = test_fn(G, W)
        c.record(ok, ce)
    return c


def test_r9_psd_n6(G, W):
    Lsig = laplacian_signed(G, W)
    ev = np.linalg.eigvalsh(Lsig)
    ok = bool(np.min(ev) > -1e-6)
    return ok, None if ok else {**describe(G, W), "min_eig": float(np.min(ev))}


def test_r10_gap_n6(G, W):
    Lsig = laplacian_signed(G, W)
    ev = np.linalg.eigvalsh(Lsig)
    has_zero = bool(np.min(np.abs(ev)) < 1e-6)
    bal = beta(G, W) >= 1
    ok = has_zero == bal
    return ok, None if ok else {**describe(G, W), "min_eig": float(np.min(ev))}


def test_r11_trace_sq(G, W):
    Lm = laplacian_mobius(G, W); Ls = laplacian_scalar(G); Lsig = laplacian_signed(G, W)
    lhs = float(np.trace(Lm @ Lm))
    rhs = float(np.trace(Ls @ Ls) + np.trace(Lsig @ Lsig))
    ok = abs(lhs - rhs) < 1e-5
    return ok, None if ok else {**describe(G, W), "lhs": lhs, "rhs": rhs}


def test_r14_fiber_rank(G, W):
    for comp in nx.connected_components(G):
        H = G.subgraph(comp).copy()
        Hrl, Wrl = relabel(H, W)
        Lm = laplacian_mobius(Hrl, Wrl)
        r = int(np.linalg.matrix_rank(Lm, tol=1e-8))
        size = 2 * Hrl.number_of_nodes()
        expected = size - (1 + (1 if is_balanced_component(Hrl, Wrl) else 0))
        if r != expected:
            return False, {**describe(G, W), "comp": sorted(comp),
                           "rank": r, "expected": expected}
    return True, None


def test_r17_interlacing(G, W):
    for e in edge_list(G):
        if e in W:
            continue
        Ge = G.copy(); Ge.remove_edge(*e)
        ev_G = sorted(np.linalg.eigvalsh(laplacian_signed(G, W)))
        ev_Ge = sorted(np.linalg.eigvalsh(laplacian_signed(Ge, W)))
        for i in range(len(ev_G) - 1):
            if not (ev_Ge[i] - 1e-5 <= ev_G[i] <= ev_Ge[i + 1] + 1e-5):
                return False, {**describe(G, W), "removed_edge": list(e)}
    return True, None


def test_r21_wrap_bipartite(G, W):
    if not nx.is_connected(G):
        return True, None  # vacuous; precondition not met
    if not is_balanced_component(G, W):
        return True, None  # vacuous
    H = nx.Graph(); H.add_nodes_from(G.nodes()); H.add_edges_from(W)
    ok = nx.is_bipartite(H)
    return ok, None if ok else {**describe(G, W)}


def main():
    tests = {
        "R9_n6": test_r9_psd_n6,
        "R10_n6": test_r10_gap_n6,
        "R11_n6": test_r11_trace_sq,
        "R14_n6": test_r14_fiber_rank,
        "R17_n6": test_r17_interlacing,
        "R21_n6": test_r21_wrap_bipartite,
    }
    out = []
    for name, fn in tests.items():
        c = check_claim(name, fn)
        print(f"{name}: tau={c.tau:.4f}  ({c.passed}/{c.tested})")
        out.append(c.to_dict())
    Path(__file__).with_name("results_n6.json").write_text(
        json.dumps(out, indent=2, default=str))


if __name__ == "__main__":
    main()
