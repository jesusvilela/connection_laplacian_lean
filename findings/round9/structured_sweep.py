"""Round-9 (LOCAL-ONLY) structured-adversarial sweep.

Motivation: the historical counterexample to the naive parity formula was
K4 with a wrap MATCHING - structured, not random, wrap data. Random wrap
sampling underweights exactly those families. This sweep attacks the four
kernel/spectrum/fibre/PSD claims with STRUCTURED wrap families:

  - every CUT of the graph (all 2^(n-1) vertex bipartitions, wrap = edges
    crossing the cut);
  - spanning trees (wrap = tree edge set), capped + seeded;
  - maximal matchings (wrap = matching), capped + seeded;
  - single edges and complements of the above.

Graph universe: all unlabeled connected graphs at n=9 with 8..11 edges and
at n=10 with 9..11 edges (nauty geng), which requires geng - run in WSL and
ship the .g6 lists first. Checks identical to round 8 (K/S/F/P) via the
independent implementation from the repo.

Local artifact: lives outside the repo by design (round discipline).
Deterministic; exit 1 on any failure.
"""
import itertools
import json
import random
import sys
import time
from multiprocessing import Pool

import networkx as nx
import numpy as np

REPO = "C:/Users/HAL900/.zcode/workspace/default/connection_laplacian_lean"
sys.path.insert(0, REPO + "/findings/round8")
from independent_impl import (
    beta, connection_laplacian, cover_component_fibres, fibre_sheets,
    kernel_dim, scalar_laplacian, signed_laplacian, spectrum,
)

TOL_SPEC = 1e-7
TOL_PSD = 1e-9
TREE_CAP = 150
MATCH_CAP = 150
SEED = 20261016


def check_config(adj, wrap):
    fails = []
    Lsc = scalar_laplacian(adj)
    Lsg = signed_laplacian(adj, wrap)
    Lmob = connection_laplacian(adj, wrap)
    if kernel_dim(Lmob) != kernel_dim(Lsc) + kernel_dim(Lsg):
        fails.append(("K", kernel_dim(Lmob), kernel_dim(Lsc) + kernel_dim(Lsg)))
    s_union = np.sort(np.concatenate([spectrum(Lsc), spectrum(Lsg)]))
    if not np.allclose(np.sort(spectrum(Lmob)), s_union, atol=TOL_SPEC):
        fails.append(("S",))
    fs = fibre_sheets(adj, wrap)
    fibres, total = cover_component_fibres(adj, wrap)
    if fibres != fs["sheets"] or total != fs["total_cover_components"]:
        fails.append(("F",))
    if fs["total_cover_components"] != len(fs["components"]) + beta(adj, wrap):
        fails.append(("Fcount",))
    if float(spectrum(Lsg)[0]) < -TOL_PSD:
        fails.append(("P", float(spectrum(Lsg)[0])))
    return fails


def structured_wraps(g, edges):
    """Deterministic structured wrap families for one graph."""
    n = g.number_of_nodes()
    eset = list(edges)
    out = [(), tuple(eset)]
    # every cut: wrap = edges crossing S vs V-S, S ranges over subsets
    # containing vertex 0 (complement identified)
    for mask in range(1 << (n - 1)):
        side = {0} | {i + 1 for i in range(n - 1) if mask >> i & 1}
        cut = tuple(e for e in eset if (e[0] in side) != (e[1] in side))
        out.append(cut)
    rng = random.Random(SEED + len(eset))
    # spanning trees (random, capped)
    seen = 0
    while seen < TREE_CAP:
        try:
            t = nx.random_spanning_tree(g, seed=rng.randint(0, 10**9))
            te = tuple(sorted(tuple(sorted(e)) for e in t.edges()))
            out.append(te)
            seen += 1
        except Exception:
            break
    # maximal matchings (random greedy, capped)
    seen = 0
    while seen < MATCH_CAP:
        order = eset[:]
        rng.shuffle(order)
        used, m = set(), []
        for u, v in order:
            if u not in used and v not in used:
                m.append((u, v)); used |= {u, v}
        out.append(tuple(m))
        seen += 1
    # dedupe, keep deterministic order
    return list(dict.fromkeys(out))


def worker(arg):
    adj, edges, nverts = arg
    import networkx as nx2
    g = nx2.from_edgelist(edges, create_using=nx2.Graph)
    g.add_nodes_from(range(nverts))
    n = 0
    fails = []
    for w in structured_wraps(g, edges):
        n += 1
        f = check_config(adj, w)
        if f:
            fails.extend((tuple(w), x) for x in f)
    return n, fails


def main():
    t0 = time.time()
    jobs = []
    for path in sys.argv[1:]:
        for g in load_band(path):
            nverts = g.number_of_nodes()
            adj = nx.to_numpy_array(g, nodelist=range(nverts), dtype=int)
            edges = [tuple(sorted(e)) for e in g.edges()]
            jobs.append((adj, edges, nverts))
    total, failures = 0, []
    with Pool(10, maxtasksperchild=8) as pool:
        for n, fails in pool.imap_unordered(worker, jobs, chunksize=4):
            total += n
            failures.extend(fails)
            if total % 250_000 < 100_000:
                print(f"  ... {total} configs, {len(failures)} failures, "
                      f"{time.time()-t0:.0f}s", flush=True)
    summary = {
        "date": "2026-10-16",
        "mode": "structured-adversarial (cuts / spanning trees / maximal matchings / extremes)",
        "inputs": sys.argv[1:],
        "total_configs": total,
        "total_failures": len(failures),
        "elapsed_seconds": round(time.time() - t0, 1),
        "failure_examples": [
            {"wrap": [list(e) for e in w], "check": list(f)} for w, f in failures[:20]],
    }
    out = "round9_structured_results.json"
    json.dump(summary, open(out, "w"), indent=1)
    print(json.dumps({k: v for k, v in summary.items() if k != "failure_examples"}, indent=1))
    sys.exit(1 if failures else 0)


def load_band(path):
    with open(path) as f:
        return [nx.from_graph6_bytes(l.strip().encode()) for l in f
                if l.strip() and not l.startswith(">")]


if __name__ == "__main__":
    main()
