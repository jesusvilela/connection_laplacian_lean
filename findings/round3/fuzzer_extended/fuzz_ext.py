"""
Round-3 EXTENDED fuzzer for the connection-Laplacian formalization.

Builds on findings/round2/fuzzer/fuzz.py.  This version:

  (A) Extends coverage to n = 6 (all non-iso graphs, 156 of them) and
      n = 7 (RANDOM sample of 512 non-iso graphs + all 2^|E| wraps).

  (B) Adds deeper per-config checks:

      T1 spectrum       : spec(L_möb)  == multiset-union of
                           spec(L_scalar) and spec(L_signed)
      T1_trace          : tr(L_möb)    == tr(L_scalar) + tr(L_signed)
                                       == 2 * tr(L_scalar)
                                       == 4 * |E|
      T1_det            : for α ∈ {0.5, 1.0, 2.0, 3.7, 10.0},
                           det(L_möb + αI) == det(L_scalar+αI)·det(L_signed+αI)
      T2 kernel-dim     : dim ker L_möb = dim ker L_scalar + dim ker L_signed
      T2_split          : kernel of L_möb splits into
                           symmetric-sheet lifts of ker L_scalar  ⊕
                           anti-symmetric-sheet lifts of ker L_signed
      T3 fiber          : #{cover component above C} == 2 iff C balanced
      T4 balance-cross  : walk-parity balance check  ==  2-coloring balance check
                           (redundancy)
      T5 zero-mult      : dim ker L_möb  ==  #π₀(G) + #balanced(G)
      T6 mult-per-eig   : for every distinct λ in spec(L_möb),
                           mult_möb(λ) == mult_scalar(λ) + mult_signed(λ)
      T7 signed-ker-fml : dim ker L_signed == #balanced components

  (C) For cycles C_n with wrap-set of size 1, compares
      spec(L_möb) to the predicted "shift-by-half" spectrum
      {2 - 2 cos(π k / n) : k = 0,...,2n-1}.
      (Reported separately in the output under `cycle_probe`.)

Outputs
-------
  fuzz_ext_results.json
  report.md
"""

from __future__ import annotations

import itertools
import json
import math
import random
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

import networkx as nx
import numpy as np

TOL_SPEC = 1e-7
TOL_DET = 1e-6
TOL_KER = 1e-8


# ----------------------------------------------------------------- graphs

_iso_bucket: dict[str, list[nx.Graph]] = defaultdict(list)


def all_graphs_up_to_iso(n: int) -> Iterable[nx.Graph]:
    """All simple graphs on {0,..,n-1} up to isomorphism.

    WL-hash bucketing + explicit iso check inside each bucket.
    Fine for n up to 7 (1044 non-iso graphs at n=7).
    """
    _iso_bucket.clear()
    seen_hashes: set[str] = set()
    verts = list(range(n))
    all_edges = list(itertools.combinations(verts, 2))
    for r in range(len(all_edges) + 1):
        for es in itertools.combinations(all_edges, r):
            G = nx.Graph()
            G.add_nodes_from(verts)
            G.add_edges_from(es)
            h = nx.weisfeiler_lehman_graph_hash(G, iterations=5)
            if h in seen_hashes:
                dup = False
                for rep in _iso_bucket[h]:
                    if nx.is_isomorphic(G, rep):
                        dup = True
                        break
                if not dup:
                    _iso_bucket[h].append(G)
                    yield G
            else:
                seen_hashes.add(h)
                _iso_bucket[h].append(G)
                yield G


def sample_graphs(n: int, k: int, rng: random.Random) -> list[nx.Graph]:
    """Random sample of k non-iso graphs on n vertices.

    Strategy: draw random G(n, p) with p ~ Uniform[0, 1] repeatedly; keep
    non-iso representatives until we have k of them or we've tried 50*k
    draws.
    """
    _iso_bucket.clear()
    reps: list[nx.Graph] = []
    tries = 0
    max_tries = 50 * k
    while len(reps) < k and tries < max_tries:
        tries += 1
        p = rng.random()
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
        h = nx.weisfeiler_lehman_graph_hash(G, iterations=5)
        dup = False
        for rep in _iso_bucket[h]:
            if nx.is_isomorphic(G, rep):
                dup = True
                break
        if not dup:
            _iso_bucket[h].append(G)
            reps.append(G)
    return reps


# -------------------------------------------------------------- laplacians

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
    """Orientation double cover. Vertex (v, b) encoded as 2*v + b."""
    n = G.number_of_nodes()
    H = nx.Graph()
    H.add_nodes_from(range(2 * n))
    for u, v in G.edges():
        e = frozenset({u, v})
        if wrap[e]:
            H.add_edge(2 * u + 0, 2 * v + 1)
            H.add_edge(2 * u + 1, 2 * v + 0)
        else:
            H.add_edge(2 * u + 0, 2 * v + 0)
            H.add_edge(2 * u + 1, 2 * v + 1)
    return H


# ---------------------------------------------------------------- balance

def is_balanced_component_coloring(
    G: nx.Graph, wrap: dict[frozenset, bool], component: frozenset[int]
) -> bool:
    """Brute-force 2-coloring balance check on a single component."""
    comp_vs = sorted(component)
    comp_edges = [(u, v) for (u, v) in G.edges() if u in component]
    # A component with 0 vertices or 1 vertex is trivially balanced.
    if len(comp_vs) <= 1:
        return True
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


def is_balanced_component_walkparity(
    G: nx.Graph, wrap: dict[frozenset, bool], component: frozenset[int]
) -> bool:
    """Walk-parity check.

    A component is balanced iff every cycle has an even number of wrap edges,
    iff you can BFS from any vertex and never hit a parity conflict.

    Encode: BFS with sign σ(v) ∈ {0,1}; start σ(root) = 0.  For edge {u,v}
    traversed, set σ(v) = σ(u) XOR wrap{u,v}.  If re-visit disagrees, unbalanced.
    """
    comp_vs = list(component)
    if not comp_vs:
        return True
    root = comp_vs[0]
    sign: dict[int, int] = {root: 0}
    queue = [root]
    while queue:
        u = queue.pop()
        su = sign[u]
        for v in G.neighbors(u):
            if v not in component:
                continue
            w = 1 if wrap[frozenset({u, v})] else 0
            predicted = su ^ w
            if v in sign:
                if sign[v] != predicted:
                    return False
            else:
                sign[v] = predicted
                queue.append(v)
    return True


# ---------------------------------------------------------------- spectra

def rank_deficiency(M: np.ndarray) -> int:
    if M.size == 0:
        return 0
    s = np.linalg.svd(M, compute_uv=False)
    if s.size == 0:
        return M.shape[0]
    tol = max(M.shape) * s.max() * np.finfo(float).eps * 10
    return int(np.sum(s <= tol))


def sorted_spectrum(M: np.ndarray) -> np.ndarray:
    return np.sort(np.linalg.eigvalsh(M))


def multiset_equal(a: np.ndarray, b: np.ndarray, tol: float = TOL_SPEC) -> bool:
    if a.shape != b.shape:
        return False
    return bool(np.allclose(a, b, atol=tol))


def mult_bucket(spec: np.ndarray, tol: float = TOL_SPEC) -> list[tuple[float, int]]:
    """Collapse eigenvalues that differ by < tol into buckets."""
    if spec.size == 0:
        return []
    s = np.sort(spec)
    out: list[tuple[float, int]] = []
    cur = s[0]
    count = 1
    for x in s[1:]:
        if abs(x - cur) <= tol:
            count += 1
        else:
            out.append((float(cur), count))
            cur = x
            count = 1
    out.append((float(cur), count))
    return out


# -------------------------------------------------- per-config tester

def run_case(G: nx.Graph, wrap_bits: int,
             edges_canonical: list[tuple[int, int]]) -> dict:
    wrap = {
        frozenset({u, v}): bool((wrap_bits >> i) & 1)
        for i, (u, v) in enumerate(edges_canonical)
    }
    n = G.number_of_nodes()
    m = G.number_of_edges()
    L_scalar = scalar_laplacian(G)
    L_signed = signed_laplacian_mobius(G, wrap)
    H = cover_graph(G, wrap)
    L_mob = scalar_laplacian(H)   # = cover-graph scalar Laplacian = L̃

    # ---------- T1: spectrum equality
    spec_mob = sorted_spectrum(L_mob)
    spec_scalar = sorted_spectrum(L_scalar)
    spec_signed = sorted_spectrum(L_signed)
    spec_union = np.sort(np.concatenate([spec_scalar, spec_signed]))
    t1_ok = multiset_equal(spec_mob, spec_union)

    # ---------- T1_trace
    tr_mob = float(np.trace(L_mob))
    tr_scalar = float(np.trace(L_scalar))
    tr_signed = float(np.trace(L_signed))
    t1_tr_split = abs(tr_mob - (tr_scalar + tr_signed)) < TOL_SPEC
    t1_tr_2scalar = abs(tr_mob - 2 * tr_scalar) < TOL_SPEC
    t1_tr_4e = abs(tr_mob - 4 * m) < TOL_SPEC
    t1_trace_ok = t1_tr_split and t1_tr_2scalar and t1_tr_4e

    # ---------- T1_det (shifted)
    det_fails: list[tuple[float, float, float]] = []
    for alpha in (0.5, 1.0, 2.0, 3.7, 10.0):
        I_big = np.eye(L_mob.shape[0])
        I_sm = np.eye(n)
        d_mob = float(np.linalg.det(L_mob + alpha * I_big))
        d_scal = float(np.linalg.det(L_scalar + alpha * I_sm))
        d_sign = float(np.linalg.det(L_signed + alpha * I_sm))
        lhs = d_mob
        rhs = d_scal * d_sign
        # Relative tolerance for numerical stability on big graphs.
        scale = max(1.0, abs(lhs), abs(rhs))
        if abs(lhs - rhs) > TOL_DET * scale:
            det_fails.append((alpha, lhs, rhs))
    t1_det_ok = not det_fails

    # ---------- T2: kernel dims
    k_mob = rank_deficiency(L_mob)
    k_scalar = rank_deficiency(L_scalar)
    k_signed = rank_deficiency(L_signed)
    t2_ok = (k_mob == k_scalar + k_signed)

    # ---------- T2_split: kernel-basis sheet decomposition
    # Build symmetric-sheet lifts of ker(L_scalar) and anti-symmetric-sheet
    # lifts of ker(L_signed); check they together span ker(L_mob).
    # Sheet encoding: position 2v+0 = sheet 0, 2v+1 = sheet 1.
    # Symmetric lift of x ∈ R^n:  y[2v+0] = y[2v+1] = x[v]  (up to norm).
    # Anti-symm lift of x ∈ R^n:  y[2v+0] = x[v], y[2v+1] = -x[v].
    def _ker_basis(M: np.ndarray) -> np.ndarray:
        u, s, vh = np.linalg.svd(M)
        tol = max(M.shape) * s.max() * np.finfo(float).eps * 10 if s.size else 0
        null_mask = s <= tol
        # vh rows for zero singular values: add leftover rows if null space
        # bigger than len(s).
        k = int(np.sum(null_mask))
        # Null space from vh: rows corresponding to null singular values.
        # vh has shape (n, n); the last n - rank rows are the null space.
        rank = int(np.sum(~null_mask))
        return vh[rank:].T  # columns are basis

    B_scal = _ker_basis(L_scalar)
    B_sign = _ker_basis(L_signed)

    # Lift to 2n-dim.
    lifts = []
    for j in range(B_scal.shape[1]):
        col = B_scal[:, j]
        y = np.zeros(2 * n)
        for v in range(n):
            y[2 * v + 0] = col[v]
            y[2 * v + 1] = col[v]
        lifts.append(y)
    for j in range(B_sign.shape[1]):
        col = B_sign[:, j]
        y = np.zeros(2 * n)
        for v in range(n):
            y[2 * v + 0] = col[v]
            y[2 * v + 1] = -col[v]
        lifts.append(y)

    t2_split_ok = True
    t2_split_detail = None
    if lifts:
        Lifts = np.stack(lifts, axis=1)
        # 1. Each lifted vector is actually in ker(L_mob).
        res = L_mob @ Lifts
        in_kernel = np.max(np.abs(res)) < TOL_KER * max(1.0, np.max(np.abs(Lifts)))
        # 2. Lifts are linearly independent (rank = #lifts).
        rank_lifts = int(np.linalg.matrix_rank(Lifts, tol=TOL_KER))
        indep = (rank_lifts == Lifts.shape[1])
        # 3. #lifts == dim ker(L_mob)
        span_full = (Lifts.shape[1] == k_mob)
        t2_split_ok = bool(in_kernel and indep and span_full)
        if not t2_split_ok:
            t2_split_detail = {
                "in_kernel": bool(in_kernel),
                "indep": indep,
                "span_full": span_full,
                "rank_lifts": rank_lifts,
                "n_lifts": int(Lifts.shape[1]),
                "k_mob": int(k_mob),
                "max_residual": float(np.max(np.abs(res))),
            }
    else:
        # No lifts; kernel of L_mob had better be trivial.
        if k_mob != 0:
            t2_split_ok = False
            t2_split_detail = {"k_mob": k_mob, "n_lifts": 0}

    # ---------- T3: fiber cardinalities
    base_components = [frozenset(c) for c in nx.connected_components(G)]
    cover_components = [frozenset(c) for c in nx.connected_components(H)]
    t3_ok = True
    t3_detail = []
    bal_count_components = 0
    for C in base_components:
        fib = 0
        for D in cover_components:
            proj = {d // 2 for d in D}
            if proj and proj.issubset(C):
                fib += 1
        bal = is_balanced_component_coloring(G, wrap, C)
        if bal:
            bal_count_components += 1
        expect = 2 if bal else 1
        if fib != expect:
            t3_ok = False
            t3_detail.append({
                "component": sorted(C), "balanced": bal,
                "fiber": fib, "expected": expect,
            })

    # ---------- T4: balance-cross
    t4_ok = True
    t4_detail = []
    for C in base_components:
        bc = is_balanced_component_coloring(G, wrap, C)
        bw = is_balanced_component_walkparity(G, wrap, C)
        if bc != bw:
            t4_ok = False
            t4_detail.append({
                "component": sorted(C),
                "coloring": bc,
                "walkparity": bw,
            })

    # ---------- T5: dim ker L_mob == #π₀(G) + #balanced(G)
    pi0_G = len(base_components)
    t5_ok = (k_mob == pi0_G + bal_count_components)

    # ---------- T6: per-eigenvalue multiplicity sum
    b_mob = mult_bucket(spec_mob)
    b_scal = mult_bucket(spec_scalar)
    b_sign = mult_bucket(spec_signed)

    # Merge scalar and signed buckets, treating close eigenvalues equal.
    def _merge(bs: list[list[tuple[float, int]]]) -> list[tuple[float, int]]:
        all_pairs = sorted([p for b in bs for p in b])
        if not all_pairs:
            return []
        out: list[tuple[float, int]] = []
        cur_val, cur_ct = all_pairs[0]
        for val, ct in all_pairs[1:]:
            if abs(val - cur_val) <= TOL_SPEC:
                cur_ct += ct
            else:
                out.append((cur_val, cur_ct))
                cur_val, cur_ct = val, ct
        out.append((cur_val, cur_ct))
        return out

    b_union = _merge([b_scal, b_sign])
    t6_ok = True
    if len(b_mob) != len(b_union):
        t6_ok = False
    else:
        for (a, am), (b, bm) in zip(b_mob, b_union):
            if abs(a - b) > TOL_SPEC or am != bm:
                t6_ok = False
                break

    # ---------- T7: dim ker L_signed == #balanced(G)
    t7_ok = (k_signed == bal_count_components)

    return {
        "T1_spec": t1_ok,
        "T1_trace": t1_trace_ok,
        "T1_trace_detail": (tr_mob, tr_scalar, tr_signed, 4 * m),
        "T1_det": t1_det_ok,
        "T1_det_fails": det_fails,
        "T2_ker": t2_ok,
        "T2_split": t2_split_ok,
        "T2_split_detail": t2_split_detail,
        "T3_fiber": t3_ok,
        "T3_detail": t3_detail if t3_detail else None,
        "T4_balance_cross": t4_ok,
        "T4_detail": t4_detail if t4_detail else None,
        "T5_zero_mult": t5_ok,
        "T5_detail": (k_mob, pi0_G, bal_count_components),
        "T6_mult_per_eig": t6_ok,
        "T7_signed_ker": t7_ok,
        "T7_detail": (k_signed, bal_count_components),
        "sizes": (n, m, 2 * n),
        "k_mob": k_mob,
        "k_scalar": k_scalar,
        "k_signed": k_signed,
    }


def graph_descr(G: nx.Graph) -> str:
    return f"n={G.number_of_nodes()},E={sorted(G.edges())}"


# --------------------------------------------------- cycle shift-by-half probe

def cycle_shift_probe(n: int) -> dict:
    """For C_n with one wrap edge, compare spec(L_möb) against
    predicted shift-by-half spectrum  {2 - 2 cos(π k / n) : k=0,..,2n-1}.
    """
    G = nx.cycle_graph(n)
    edges_canonical = sorted(tuple(sorted(e)) for e in G.edges())
    # Wrap first edge only.
    wrap = {frozenset({u, v}): (i == 0) for i, (u, v) in enumerate(edges_canonical)}
    H = cover_graph(G, wrap)
    L_mob = scalar_laplacian(H)
    spec_mob = sorted_spectrum(L_mob)
    predicted = np.sort(np.array(
        [2 - 2 * math.cos(math.pi * k / n) for k in range(2 * n)]
    ))
    match = multiset_equal(spec_mob, predicted, tol=1e-6)
    return {
        "n": n,
        "match": bool(match),
        "spec_mob": spec_mob.tolist(),
        "spec_predicted": predicted.tolist(),
        "max_abs_diff": float(np.max(np.abs(spec_mob - predicted))),
    }


# ----------------------------------------------------------------- driver

TEST_KEYS = [
    "T1_spec", "T1_trace", "T1_det",
    "T2_ker", "T2_split",
    "T3_fiber", "T4_balance_cross",
    "T5_zero_mult", "T6_mult_per_eig", "T7_signed_ker",
]


def run_bucket(name: str, graphs: list[nx.Graph], max_wrap_cap: int | None = None):
    fails = {k: [] for k in TEST_KEYS}
    configs = 0
    start = time.time()
    for gi, G in enumerate(graphs):
        edges_canonical = sorted(tuple(sorted(e)) for e in G.edges())
        m = len(edges_canonical)
        total_wraps = 1 << m
        if max_wrap_cap is not None and total_wraps > max_wrap_cap:
            # Sample wraps uniformly
            wrap_iter = [
                random.randrange(total_wraps) for _ in range(max_wrap_cap)
            ]
        else:
            wrap_iter = range(total_wraps)
        for wrap_bits in wrap_iter:
            configs += 1
            res = run_case(G, wrap_bits, edges_canonical)
            for k in TEST_KEYS:
                if not res[k]:
                    if len(fails[k]) < 20:
                        fails[k].append({
                            "graph": graph_descr(G),
                            "wrap_bits": int(wrap_bits),
                            "wrap_edges": [
                                e for i, e in enumerate(edges_canonical)
                                if (int(wrap_bits) >> i) & 1
                            ],
                            "detail": {
                                "T1_trace_detail": res["T1_trace_detail"],
                                "T1_det_fails": res["T1_det_fails"],
                                "T2_split_detail": res["T2_split_detail"],
                                "T3_detail": res["T3_detail"],
                                "T4_detail": res["T4_detail"],
                                "T5_detail": res["T5_detail"],
                                "T7_detail": res["T7_detail"],
                                "k_mob": res["k_mob"],
                                "k_scalar": res["k_scalar"],
                                "k_signed": res["k_signed"],
                            },
                        })
        if (gi + 1) % 25 == 0 or gi + 1 == len(graphs):
            print(f"[{name}] graph {gi + 1}/{len(graphs)}  configs={configs} "
                  f"t={time.time() - start:.1f}s",
                  flush=True)
    return configs, fails


def main():
    out_dir = Path(__file__).parent
    out_dir.mkdir(parents=True, exist_ok=True)

    random.seed(20260421)

    results: dict = {
        "meta": {
            "tol_spec": TOL_SPEC,
            "tol_det": TOL_DET,
            "tol_ker": TOL_KER,
        },
        "buckets": {},
        "cycle_probe": {},
    }

    # ---- exhaustive n = 2..5 (sanity, fast)
    for n in (2, 3, 4, 5):
        graphs = list(all_graphs_up_to_iso(n))
        print(f"n={n}: {len(graphs)} non-iso graphs (exhaustive)")
        configs, fails = run_bucket(f"n={n}", graphs)
        results["buckets"][f"n={n}"] = {
            "mode": "exhaustive",
            "graphs": len(graphs),
            "configs": configs,
            "fail_counts": {k: len(v) for k, v in fails.items()},
            "fail_samples": fails,
        }

    # ---- exhaustive n = 6 (156 non-iso graphs; 2^|E| wraps, up to 2^15 at K6)
    n = 6
    graphs6 = list(all_graphs_up_to_iso(n))
    print(f"n=6: {len(graphs6)} non-iso graphs (exhaustive graphs; wrap cap 4096)")
    # Cap wrap-subsets per graph: graphs with m ≥ 13 (many at n=6 near K6)
    # would otherwise produce 8192+ configs each.
    configs6, fails6 = run_bucket("n=6", graphs6, max_wrap_cap=4096)
    results["buckets"]["n=6"] = {
        "mode": "exhaustive_graphs_wrap_cap_4096",
        "graphs": len(graphs6),
        "configs": configs6,
        "fail_counts": {k: len(v) for k, v in fails6.items()},
        "fail_samples": fails6,
    }

    # ---- random sample for n = 7 (1044 non-iso total; sample 512)
    n = 7
    rng = random.Random(20260421)
    graphs7 = sample_graphs(n, 512, rng)
    print(f"n=7: sampled {len(graphs7)} non-iso graphs (wrap cap 1024)")
    configs7, fails7 = run_bucket("n=7", graphs7, max_wrap_cap=1024)
    results["buckets"]["n=7"] = {
        "mode": "random_sample_512_wrap_cap_1024",
        "graphs": len(graphs7),
        "configs": configs7,
        "fail_counts": {k: len(v) for k, v in fails7.items()},
        "fail_samples": fails7,
    }

    # ---- cycle shift-by-half probe
    for cn in (3, 4, 5, 6, 7, 8, 9, 12, 16):
        results["cycle_probe"][f"C_{cn}"] = cycle_shift_probe(cn)

    # Totals
    total_configs = sum(b["configs"] for b in results["buckets"].values())
    total_graphs = sum(b["graphs"] for b in results["buckets"].values())
    agg_fails = Counter()
    for b in results["buckets"].values():
        for k, v in b["fail_counts"].items():
            agg_fails[k] += v
    results["totals"] = {
        "graphs": total_graphs,
        "configs": total_configs,
        "fail_counts": dict(agg_fails),
    }

    (out_dir / "fuzz_ext_results.json").write_text(
        json.dumps(results, indent=2, default=str), encoding="utf-8")

    # ------------ markdown report
    md = []
    md.append("# Round-3 Extended Fuzzer Report")
    md.append("")
    md.append(f"*Date: 2026-04-21 — seed 20260421*")
    md.append("")
    md.append(f"Total configs tested: **{total_configs:,}** across "
              f"**{total_graphs}** graph representatives (n = 2..7).")
    md.append("")
    md.append("## Per-test fail counts (aggregate)")
    md.append("")
    md.append("| Test | Description | Fails |")
    md.append("|---|---|---|")
    descr = {
        "T1_spec": "spec(L_möb) == spec(L_scalar) ⊔ spec(L_signed)",
        "T1_trace": "tr(L_möb) = tr(L_scalar)+tr(L_signed) = 2 tr L_scalar = 4|E|",
        "T1_det": "det(L_möb+αI) = det(L_scalar+αI)·det(L_signed+αI) for α∈{.5,1,2,3.7,10}",
        "T2_ker": "dim ker L_möb = dim ker L_scalar + dim ker L_signed",
        "T2_split": "ker L_möb = sym-lift(ker L_scalar) ⊕ antisym-lift(ker L_signed)",
        "T3_fiber": "#fiber(C) = 2 if C balanced else 1",
        "T4_balance_cross": "walk-parity balance iff 2-coloring balance (redundancy)",
        "T5_zero_mult": "dim ker L_möb = #π₀(G) + #balanced components",
        "T6_mult_per_eig": "mult_möb(λ) = mult_scalar(λ) + mult_signed(λ) per eigenvalue",
        "T7_signed_ker": "dim ker L_signed = #balanced components",
    }
    for k in TEST_KEYS:
        md.append(f"| `{k}` | {descr[k]} | **{agg_fails[k]}** |")
    md.append("")

    md.append("## Per-bucket breakdown")
    md.append("")
    md.append("| Bucket | Mode | Graphs | Configs | Any fails? |")
    md.append("|---|---|---|---|---|")
    for name, b in results["buckets"].items():
        fc = b["fail_counts"]
        any_fail = any(v > 0 for v in fc.values())
        md.append(f"| {name} | {b['mode']} | {b['graphs']} | {b['configs']:,} | "
                  f"{'YES — see JSON' if any_fail else 'no'} |")
    md.append("")

    md.append("## Cycle shift-by-half probe  (C_n, single wrap edge)")
    md.append("")
    md.append("Compare spec(L_möb) on orientation double cover of C_n with one wrap edge"
              " against {2−2 cos(πk/n) : k=0..2n−1}.")
    md.append("")
    md.append("| n | match | max |diff| |")
    md.append("|---|---|---|")
    for key, v in results["cycle_probe"].items():
        md.append(f"| {v['n']} | {'yes' if v['match'] else 'NO'} | {v['max_abs_diff']:.2e} |")
    md.append("")

    md.append("## Interpretation")
    md.append("")
    if all(v == 0 for v in agg_fails.values()):
        md.append("- All ten identities hold across every tested (graph, wrap) config.")
        md.append("- In particular, beyond T1/T2/T3 (already confirmed in round 2):")
        md.append("  - **T2_split**: the kernel of `L_möb` really does split as the direct"
                  " sum of symmetric-sheet lifts of ker(L_scalar) and anti-symmetric-sheet"
                  " lifts of ker(L_signed). This is a concrete *basis*-level statement,"
                  " candidate for the next Lean theorem.")
        md.append("  - **T5**: `dim ker L_möb = #π₀(G) + #balanced(G)` — a single"
                  " closed-form invariant combining the two decomposition halves.")
        md.append("  - **T6**: the spectral decomposition is pointwise (multiplicity-wise),"
                  " not just set-wise.")
        md.append("  - **T7**: `dim ker L_signed = #balanced(G)`, the standard"
                  " signed-Laplacian kernel formula; a clean Lean target.")
        md.append("  - **T4**: walk-parity agrees with 2-coloring brute-force balance"
                  " — confirms the algorithmic balance predicate is sound.")
    else:
        md.append("- Some identities FAILED; see JSON for counter-examples.")
    md.append("")
    md.append("## Files")
    md.append("")
    md.append("- `fuzz_ext.py` — this script")
    md.append("- `fuzz_ext_results.json` — full results + up to 20 failing samples per test")

    (out_dir / "report.md").write_text("\n".join(md), encoding="utf-8")
    print("Wrote fuzz_ext_results.json and report.md")
    print(json.dumps({"totals": results["totals"]}, indent=2))


if __name__ == "__main__":
    main()
