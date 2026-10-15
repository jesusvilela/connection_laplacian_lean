"""Round-8 n=8 sweep: bounded-exhaustive falsification pressure, computed
ENTIRELY with the INDEPENDENT paper-only implementation
(independent_impl.py, written from paper.tex alone — no Lean sources, no
prior fuzzers).

Coverage (all graphs unlabeled, vertices Fin 8):
  - band A: ALL connected graphs with 7..12 edges, ALL 2^e wrap subsets
            (23+89+236+486+814+1169 = 2817 graphs, 7,099,520 configurations)
  - band B: ALL graphs (connected or not) with 0..7 edges, ALL 2^e wraps
            (215 graphs, 19,299 configurations)
  - band C: 2000 seeded random graphs G(8, 1/2) x 64 seeded random wraps
            (128k configurations, covers densities e>12 up to K8)

Checks per configuration (all via the independent implementation):
  K  kernel-dim additivity:   dim ker L_Mob = dim ker L_sc + dim ker L_sig
  S  spectrum multiset union: spec(L_Mob) = spec(L_sc) + spec(L_sig)
  F  fibres: per base component, cover fibre = 2 iff balanced else 1
             (colouring route vs explicit cover construction), and
             #comp(cover) = #comp(base) + beta
  P  PSD: min eig(L_sig) >= -1e-9

Deterministic; exit code 1 if any failure.
"""
import itertools
import json
import random
import sys
import time
from multiprocessing import Pool

import networkx as nx
import numpy as np

sys.path.insert(0, "findings/round8")
from independent_impl import (
    beta, connection_laplacian, cover_component_fibres, fibre_sheets,
    kernel_dim, scalar_laplacian, signed_laplacian, spectrum,
)

TOL_SPEC = 1e-7
TOL_PSD = 1e-9


def load_band(path):
    with open(path) as f:
        return [nx.from_graph6_bytes(line.strip().encode())
                for line in f if line.strip() and not line.startswith(">")]


def check_config(adj, wrap):
    fails = []
    Lsc = scalar_laplacian(adj)
    Lsg = signed_laplacian(adj, wrap)
    Lmob = connection_laplacian(adj, wrap)

    k_theory = kernel_dim(Lsc) + kernel_dim(Lsg)
    k_actual = kernel_dim(Lmob)
    if k_actual != k_theory:
        fails.append(("K", int(k_actual), int(k_theory)))

    s_union = np.sort(np.concatenate([spectrum(Lsc), spectrum(Lsg)]))
    s_actual = np.sort(spectrum(Lmob))
    if not np.allclose(s_actual, s_union, atol=TOL_SPEC):
        fails.append(("S", s_actual.tolist(), s_union.tolist()))

    fs = fibre_sheets(adj, wrap)
    fibres, total_meas = cover_component_fibres(adj, wrap)
    if fibres != fs["sheets"] or total_meas != fs["total_cover_components"]:
        fails.append(("F", fibres, fs["sheets"], total_meas,
                      fs["total_cover_components"]))
    ncomp = len(fs["components"])
    if fs["total_cover_components"] != ncomp + beta(adj, wrap):
        fails.append(("Fcount", fs["total_cover_components"],
                      ncomp + beta(adj, wrap)))

    if float(spectrum(Lsg)[0]) < -TOL_PSD:
        fails.append(("P", float(spectrum(Lsg)[0])))
    return fails


def all_wraps(edges):
    return itertools.chain.from_iterable(
        itertools.combinations(edges, k) for k in range(len(edges) + 1))


def worker(arg):
    adj, edges, wrap_list = arg
    n = 0
    fails = []
    wraps = wrap_list if wrap_list is not None else all_wraps(edges)
    for w in wraps:
        n += 1
        f = check_config(adj, w)
        if f:
            fails.extend((tuple(w), x) for x in f)
    return n, fails


def main():
    t0 = time.time()
    jobs = []

    for e in range(7, 13):
        G = load_band(f"findings/round8/graphs/g8_e{e}.g6")
        for g in G:
            adj = nx.to_numpy_array(g, nodelist=range(8), dtype=int)
            edges = [tuple(sorted(e)) for e in g.edges()]
            jobs.append((adj, edges, None))

    for g in load_band("findings/round8/graphs/g8_all_e0to7.g6"):
        adj = nx.to_numpy_array(g, nodelist=range(8), dtype=int)
        edges = [tuple(sorted(e)) for e in g.edges()]
        jobs.append((adj, edges, None))

    rng = random.Random(20261015)
    for _ in range(2000):
        g = nx.gnp_random_graph(8, 0.5, seed=rng.randint(0, 10**9))
        adj = nx.to_numpy_array(g, nodelist=range(8), dtype=int)
        edges = [tuple(sorted(e)) for e in g.edges()]
        if not edges:
            continue
        wlist = []
        for _ in range(64):
            wlist.append(tuple(rng.sample(edges, rng.randint(0, len(edges)))))
        jobs.append((adj, edges, wlist))

    total = 0
    failures = []
    with Pool(10) as pool:
        for n, fails in pool.imap_unordered(worker, jobs, chunksize=8):
            total += n
            failures.extend(fails)
            if total % 500_000 < 200_000:
                print(f"  ... {total} configs, {len(failures)} failures, "
                      f"{time.time()-t0:.0f}s", flush=True)

    dt = time.time() - t0
    summary = {
        "date": "2026-10-15",
        "implementation": "independent (paper-only, findings/round8/independent_impl.py)",
        "bands": {
            "A_all_connected_e7to12_all_wraps": "2817 graphs / 7,099,520 configs",
            "B_all_graphs_e0to7_all_wraps": "215 graphs / 19,299 configs",
            "C_random_dense": "2000 graphs x 64 wraps",
        },
        "total_configs": total,
        "total_failures": len(failures),
        "elapsed_seconds": round(dt, 1),
        "failure_examples": [
            {"wrap": [list(e) for e in w], "check": f} for w, f in failures[:20]
        ],
    }
    with open("findings/round8/sweep_n8_results.json", "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps({k: v for k, v in summary.items()
                      if k != "failure_examples"}, indent=1))
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
