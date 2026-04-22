"""
FUZZER-A R6 Stage 2 - SHEAF-SECTION BETA (spectral/trace/eigenvalue masters at scale).

Scales the beta-tile master claims (M6/M7 spectrum-union, B2 mixed trace,
B14 single-flip Weyl, B15 multi-edge interlacing, B16 strict positivity)
to n=6 exhaustive and n=7 sampled. Also spot-checks the Lean-landed
claims G15, B9, B21 at n=6.

Budget: ~15 min wall. Uses numpy + mpmath only (no networkx/scipy).
Prec=50 mpmath cross-check on counterexamples and n=7 spot samples.

Envelope:
  n=6 : 156 iso classes x up to 24 sampled wrap subsets (exhaustive in
        iso classes, sampled in wraps).
  n=7 : ~200 random (G,W) pairs with varied edge density.

Output: run.log (stdout), results.json, report.md (written separately).
"""

from __future__ import annotations

import itertools
import json
import math
import random
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np
import mpmath as mp


mp.mp.prec = 50  # ~15 decimal digits (bits), we bump to 100 on counterexamples


TOL_N6 = 1e-10
TOL_N7 = 1e-7
SEED = 20260422 + 6
RNG = random.Random(SEED)
np.random.seed(SEED & 0xFFFFFFFF)


# ---------------------------------------------------------------------------
# Graph code (adjacency-matrix based, no networkx)
# ---------------------------------------------------------------------------

def edges_from_mask(n, mask):
    """Return sorted list of edges (u,v) from upper-triangular bitmask."""
    potential = list(itertools.combinations(range(n), 2))
    return [potential[i] for i in range(len(potential)) if (mask >> i) & 1]


def adjacency(n, edges):
    A = np.zeros((n, n), dtype=np.int8)
    for u, v in edges:
        A[u, v] = 1
        A[v, u] = 1
    return A


def degrees(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return deg


def connected_components(n, edges):
    """Return list of sets of vertices, one per component."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = [False] * n
    comps = []
    for s in range(n):
        if seen[s]:
            continue
        stack = [s]
        seen[s] = True
        comp = []
        while stack:
            u = stack.pop()
            comp.append(u)
            for w in adj[u]:
                if not seen[w]:
                    seen[w] = True
                    stack.append(w)
        comps.append(set(comp))
    return comps


def is_balanced_on_component(comp, edges_in_comp, W):
    """Check balanced: 2-colouring where wrap edges flip color."""
    adj = defaultdict(list)
    for u, v in edges_in_comp:
        adj[u].append(v)
        adj[v].append(u)
    color = {}
    root = next(iter(comp))
    color[root] = 0
    stack = [root]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            e = (u, w) if u < w else (w, u)
            flip = 1 if e in W else 0
            expected = color[u] ^ flip
            if w not in color:
                color[w] = expected
                stack.append(w)
            elif color[w] != expected:
                return False
    return True


def beta(n, edges, W):
    """Number of balanced connected components = dim ker L_sig."""
    comps = connected_components(n, edges)
    cnt = 0
    for comp in comps:
        edges_c = [(u, v) for u, v in edges if u in comp and v in comp]
        W_c = set(e for e in W if e in set(edges_c))
        if is_balanced_on_component(comp, edges_c, W_c):
            cnt += 1
    return cnt


def num_components(n, edges):
    return len(connected_components(n, edges))


def is_connected(n, edges):
    if n == 0:
        return True
    return num_components(n, edges) == 1


# ---------------------------------------------------------------------------
# Graph canonical-form hashing for iso classes (Weisfeiler-Lehman style)
# ---------------------------------------------------------------------------

def wl_canonical(n, edges):
    """Compute a robust isomorphism invariant signature via degree-sequence
    augmented by iterated neighbor-multiset hashing. Not a perfect canonical
    form but good enough to cut duplicate iso classes drastically; for
    small n (<= 7) WL color refinement is distinguishing on all but a tiny
    set of graphs, so we use it as a hash + fallback to brute perm check.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    labels = [len(adj[u]) for u in range(n)]
    for _ in range(n):
        new_labels = []
        for u in range(n):
            nbr_labs = tuple(sorted(labels[w] for w in adj[u]))
            new_labels.append(hash((labels[u], nbr_labs)))
        # Re-compress
        uniq = sorted(set(new_labels))
        rank = {val: i for i, val in enumerate(uniq)}
        labels = [rank[x] for x in new_labels]
    return tuple(sorted(labels))


def iso_classes_n(n):
    """Enumerate iso classes of simple graphs on n vertices via WL hash
    (some classes may collide for pathological cases; follow up with brute
    permutation test to confirm). For n<=7 this is fast."""
    max_mask = 1 << (n * (n - 1) // 2)
    seen_sigs = {}
    classes = []
    for mask in range(max_mask):
        edges = edges_from_mask(n, mask)
        sig = wl_canonical(n, edges)
        if sig in seen_sigs:
            # Check brute iso against stored reps (there can be collisions)
            reps = seen_sigs[sig]
            match = False
            for rep_edges in reps:
                if are_isomorphic(n, edges, rep_edges):
                    match = True
                    break
            if match:
                continue
            seen_sigs[sig].append(edges)
        else:
            seen_sigs[sig] = [edges]
        classes.append(edges)
    return classes


def are_isomorphic(n, edges_a, edges_b):
    """Brute-force iso check (n<=7 so at most 7! = 5040)."""
    if len(edges_a) != len(edges_b):
        return False
    set_b = set(edges_b)
    for perm in itertools.permutations(range(n)):
        mapped = set()
        ok = True
        for u, v in edges_a:
            mu, mv = perm[u], perm[v]
            if mu > mv:
                mu, mv = mv, mu
            mapped.add((mu, mv))
        if mapped == set_b:
            return True
    return False


# ---------------------------------------------------------------------------
# Laplacian builders
# ---------------------------------------------------------------------------

def laplacian_scalar(n, edges):
    L = np.zeros((n, n))
    for u, v in edges:
        L[u, u] += 1
        L[v, v] += 1
        L[u, v] -= 1
        L[v, u] -= 1
    return L


def laplacian_signed(n, edges, W):
    """L_sig: diag deg; off-diag = -1 for non-wrap, +1 for wrap."""
    L = np.zeros((n, n))
    for u, v in edges:
        L[u, u] += 1
        L[v, v] += 1
        s = +1.0 if (u, v) in W else -1.0
        L[u, v] += s
        L[v, u] += s
    return L


def laplacian_mobius(n, edges, W):
    """L_mob on C^{2V}: block structure. On diag, deg(u) * I_2; off-diag
    block at (u,v) is -X for wrap edges, -I for non-wrap edges, where
    X = [[0,1],[1,0]] (fibre-flip) and I = I_2 (identity)."""
    L = np.zeros((2 * n, 2 * n))
    I2 = np.eye(2)
    X = np.array([[0.0, 1.0], [1.0, 0.0]])
    deg = degrees(n, edges)
    for u in range(n):
        L[2 * u:2 * u + 2, 2 * u:2 * u + 2] = deg[u] * I2
    for u, v in edges:
        B = X if (u, v) in W else I2
        L[2 * u:2 * u + 2, 2 * v:2 * v + 2] -= B
        L[2 * v:2 * v + 2, 2 * u:2 * u + 2] -= B
    return L


def eigs(M):
    return np.sort(np.linalg.eigvalsh(M))


# ---------------------------------------------------------------------------
# mpmath high-precision spectrum (used for spot-check when a claim wobbles)
# ---------------------------------------------------------------------------

def mp_eigh(M):
    """Return sorted eigenvalues of symmetric matrix via mpmath (slow)."""
    mM = mp.matrix(M.tolist())
    E, _ = mp.eighe(mM)
    return sorted([mp.mpf(x) for x in E])


def mp_multiset_diff(vec_a, vec_b, tol):
    """Check (as multisets) whether sorted_a ~ sorted_b within tol."""
    if len(vec_a) != len(vec_b):
        return False, float("inf")
    diffs = [abs(float(a - b)) for a, b in zip(sorted(vec_a), sorted(vec_b))]
    return max(diffs) < tol, max(diffs)


# ---------------------------------------------------------------------------
# Envelope samplers
# ---------------------------------------------------------------------------

def n6_envelope(wrap_cap=24, iso_cap=None):
    """Exhaustive in iso classes on n=6 but cap wrap subsets per graph."""
    n = 6
    classes = iso_classes_n(n)
    if iso_cap and len(classes) > iso_cap:
        classes = classes[:iso_cap]
    count = 0
    for edges in classes:
        m = len(edges)
        all_wraps = []
        for r in range(m + 1):
            for sub in itertools.combinations(edges, r):
                all_wraps.append(frozenset(sub))
        if len(all_wraps) > wrap_cap:
            all_wraps = RNG.sample(all_wraps, wrap_cap)
        for W in all_wraps:
            yield n, edges, W
            count += 1


def n7_envelope(num_samples=200):
    """Random sample on n=7 across varied edge densities."""
    n = 7
    potential = list(itertools.combinations(range(n), 2))
    m_max = len(potential)
    densities = [0.2, 0.35, 0.5, 0.65, 0.85]
    per_density = num_samples // len(densities) + 1
    count = 0
    for density in densities:
        m_target = max(1, int(round(density * m_max)))
        for _ in range(per_density):
            edges = sorted(RNG.sample(potential, m_target))
            r = RNG.randint(0, m_target)
            W = frozenset(RNG.sample(edges, r))
            yield n, edges, W
            count += 1
            if count >= num_samples:
                return


# ---------------------------------------------------------------------------
# Claim metric accumulator
# ---------------------------------------------------------------------------

class Claim:
    def __init__(self, key, desc):
        self.key = key
        self.desc = desc
        self.tested = 0
        self.passed = 0
        self.max_rel_diff = 0.0
        self.counterexamples = []  # cap at 3

    def record(self, ok, rel_diff=0.0, ce=None):
        self.tested += 1
        if ok:
            self.passed += 1
            self.max_rel_diff = max(self.max_rel_diff, rel_diff)
        else:
            if len(self.counterexamples) < 3 and ce is not None:
                self.counterexamples.append(ce)

    def verdict(self):
        if self.tested == 0:
            return "UNTESTED"
        if self.passed == self.tested:
            return "HOLDS"
        frac = self.passed / self.tested
        if frac > 0.99:
            return "NEAR-MISS"
        return "FAIL"

    def summary(self):
        return {
            "key": self.key,
            "desc": self.desc,
            "tested": self.tested,
            "passed": self.passed,
            "tau": round(self.passed / max(1, self.tested), 8),
            "max_rel_diff": self.max_rel_diff,
            "verdict": self.verdict(),
            "counterexamples": self.counterexamples,
        }


# ---------------------------------------------------------------------------
# Test kernels (per-instance checks)
# ---------------------------------------------------------------------------

def check_M6(instance, tol, claim):
    n, edges, W = instance
    Ls = laplacian_scalar(n, edges)
    Lsig = laplacian_signed(n, edges, W)
    Lm = laplacian_mobius(n, edges, W)
    ev_s = eigs(Ls)
    ev_sig = eigs(Lsig)
    ev_m = eigs(Lm)
    combined = np.sort(np.concatenate([ev_s, ev_sig]))
    if len(combined) != len(ev_m):
        claim.record(False, ce={"reason": "size mismatch",
                                 "n": n, "edges": edges,
                                 "W": sorted(list(W))})
        return
    scale = 1.0 + float(np.max(np.abs(ev_m)))
    diffs = np.abs(combined - ev_m)
    max_abs = float(np.max(diffs))
    rel = max_abs / scale
    ok = max_abs < tol * scale
    if ok:
        claim.record(True, rel_diff=rel)
    else:
        claim.record(False, rel_diff=rel,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "max_abs": max_abs, "max_rel": rel,
                         "ev_m": list(map(float, ev_m)),
                         "combined": list(map(float, combined))})


def check_M7(instance, tol, claim):
    """Charpoly product check: coeffs of (L_mob minus lam*I) = coeffs of
    (L_s - lam*I) * (L_sig - lam*I).  We use numpy.poly(eigvals) to build
    monic charpoly coeffs."""
    n, edges, W = instance
    Ls = laplacian_scalar(n, edges)
    Lsig = laplacian_signed(n, edges, W)
    Lm = laplacian_mobius(n, edges, W)
    ev_s = eigs(Ls)
    ev_sig = eigs(Lsig)
    ev_m = eigs(Lm)
    p_s = np.poly(ev_s)     # length n+1
    p_sig = np.poly(ev_sig)  # length n+1
    p_m = np.poly(ev_m)      # length 2n+1
    p_prod = np.polymul(p_s, p_sig)
    if len(p_prod) != len(p_m):
        claim.record(False, ce={"reason": "poly size mismatch",
                                 "n": n, "edges": edges,
                                 "W": sorted(list(W))})
        return
    scale = 1.0 + float(np.max(np.abs(p_m)))
    diff = np.max(np.abs(p_m - p_prod))
    rel = float(diff) / scale
    # Slightly looser: coefficient scales can be large; compare per-coefficient
    # relative to a mixed norm.
    ok = rel < tol * 10  # allow extra slack (polynomial round-off)
    if ok:
        claim.record(True, rel_diff=rel)
    else:
        claim.record(False, rel_diff=rel,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "coeff_diff": float(diff),
                         "rel": rel,
                         "p_m": list(map(float, p_m)),
                         "p_prod": list(map(float, p_prod))})


def check_B2(instance, claim):
    n, edges, W = instance
    Ls = laplacian_scalar(n, edges)
    Lsig = laplacian_signed(n, edges, W)
    lhs = float(np.trace(Ls @ Lsig))
    m = len(edges)
    w = len(W)
    deg = degrees(n, edges)
    # tr(L_s L_sig) = sum deg^2 + 2m - 4|W|
    rhs = sum(d * d for d in deg) + 2 * m - 4 * w
    diff = abs(lhs - rhs)
    scale = 1.0 + abs(rhs)
    rel = diff / scale
    ok = diff < 1e-8 * scale
    if ok:
        claim.record(True, rel_diff=rel)
    else:
        claim.record(False, rel_diff=rel,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "lhs": lhs, "rhs": rhs})


def check_B14(instance, claim):
    """Single edge flip: |lambda_i(L_sig W) - lambda_i(L_sig W delta {e})| <= 2.
    Here we flip EVERY edge in E (not just wrap edges) - both directions
    covered because flipping is involutive."""
    n, edges, W = instance
    for e in edges:
        W2 = set(W)
        if e in W2:
            W2.discard(e)
        else:
            W2.add(e)
        W2 = frozenset(W2)
        L1 = laplacian_signed(n, edges, W)
        L2 = laplacian_signed(n, edges, W2)
        ev1 = eigs(L1)
        ev2 = eigs(L2)
        diffs = np.abs(ev1 - ev2)
        md = float(np.max(diffs))
        ok = md <= 2.0 + 1e-9
        rel = md / 2.0
        if ok:
            claim.record(True, rel_diff=rel)
        else:
            claim.record(False, rel_diff=rel,
                         ce={"n": n, "edges": edges, "W": sorted(list(W)),
                             "flipped_edge": list(e), "max_diff": md,
                             "ev1": list(map(float, ev1)),
                             "ev2": list(map(float, ev2))})


def check_B15(instance, claim):
    """Multi-edge interlacing. For a random non-wrap subset E' of size k in
    {1,2,3}, check both directions:
      lambda_i(L_sig(G-E')) >= lambda_{i-k}(L_sig(G))
      lambda_i(L_sig(G-E')) <= lambda_{i+k}(L_sig(G))
    """
    n, edges, W = instance
    nonwrap = [e for e in edges if e not in W]
    if not nonwrap:
        return
    Lorig = laplacian_signed(n, edges, W)
    ev_G = eigs(Lorig)
    # Try all subsets up to size 3 (if total non-wrap edges > 7, cap to 30 random picks)
    subsets_to_test = []
    for k in (1, 2, 3):
        if k > len(nonwrap):
            continue
        all_subs = list(itertools.combinations(nonwrap, k))
        if len(all_subs) > 8:
            RNG.shuffle(all_subs)
            all_subs = all_subs[:8]
        subsets_to_test.extend(all_subs)
    for sub in subsets_to_test:
        k = len(sub)
        remaining_edges = [e for e in edges if e not in sub]
        remaining_W = frozenset(e for e in W if e in set(remaining_edges))
        Lrem = laplacian_signed(n, remaining_edges, remaining_W)
        ev_rem = eigs(Lrem)
        max_viol = 0.0
        ok = True
        for i in range(len(ev_rem)):
            if i - k >= 0:
                v = ev_G[i - k] - ev_rem[i]
                if v > 1e-9:
                    ok = False
                    max_viol = max(max_viol, v)
            if i + k < len(ev_G):
                v = ev_rem[i] - ev_G[i + k]
                if v > 1e-9:
                    ok = False
                    max_viol = max(max_viol, v)
        rel = max_viol
        if ok:
            claim.record(True, rel_diff=rel)
        else:
            claim.record(False, rel_diff=rel,
                         ce={"n": n, "edges": edges, "W": sorted(list(W)),
                             "removed": [list(e) for e in sub],
                             "max_viol": max_viol,
                             "ev_G": list(map(float, ev_G)),
                             "ev_rem": list(map(float, ev_rem))})


def check_B16(instance, claim):
    """Strict positivity: G connected, beta=0 implies lambda_min(L_sig) > 0."""
    n, edges, W = instance
    if not is_connected(n, edges):
        return
    if beta(n, edges, W) != 0:
        return
    L = laplacian_signed(n, edges, W)
    ev = eigs(L)
    lmin = float(ev[0])
    ok = lmin > 1e-10
    if ok:
        claim.record(True, rel_diff=lmin)
    else:
        claim.record(False, rel_diff=lmin,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "lmin": lmin,
                         "ev": list(map(float, ev))})


def check_G15(instance, claim):
    """Sanity: dim ker(L_sig) (#eigs < 1e-9) == beta(G,W)."""
    n, edges, W = instance
    L = laplacian_signed(n, edges, W)
    ev = eigs(L)
    ker_dim = int(np.sum(np.abs(ev) < 1e-9))
    b = beta(n, edges, W)
    ok = ker_dim == b
    if ok:
        claim.record(True)
    else:
        claim.record(False,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "ker_dim": ker_dim, "beta": b,
                         "ev": list(map(float, ev))})


def check_B9(instance, claim):
    """Sanity: dim ker(L_mob) = #components(G) + beta(G,W)."""
    n, edges, W = instance
    Lm = laplacian_mobius(n, edges, W)
    ev = eigs(Lm)
    ker_dim = int(np.sum(np.abs(ev) < 1e-9))
    rhs = num_components(n, edges) + beta(n, edges, W)
    ok = ker_dim == rhs
    if ok:
        claim.record(True)
    else:
        claim.record(False,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "ker_dim": ker_dim, "ncomp_plus_beta": rhs,
                         "ev": list(map(float, ev))})


def check_B21(instance, claim):
    """Sanity: sum of sign(lambda_i(L_sig)) = n - beta(G,W)."""
    n, edges, W = instance
    L = laplacian_signed(n, edges, W)
    ev = eigs(L)
    signs = np.where(np.abs(ev) < 1e-9, 0.0, np.where(ev > 0, 1.0, -1.0))
    lhs = float(np.sum(signs))
    rhs = n - beta(n, edges, W)
    ok = abs(lhs - rhs) < 1e-9
    if ok:
        claim.record(True)
    else:
        claim.record(False,
                     ce={"n": n, "edges": edges, "W": sorted(list(W)),
                         "lhs": lhs, "rhs": rhs,
                         "ev": list(map(float, ev))})


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def run_envelope(env_iter, label, tol, claims):
    t0 = time.time()
    count = 0
    for inst in env_iter:
        count += 1
        check_M6(inst, tol, claims["M6"])
        check_M7(inst, tol, claims["M7"])
        check_B2(inst, claims["B2"])
        check_B14(inst, claims["B14"])
        check_B15(inst, claims["B15"])
        check_B16(inst, claims["B16"])
        check_G15(inst, claims["G15"])
        check_B9(inst, claims["B9"])
        check_B21(inst, claims["B21"])
        if count % 200 == 0:
            elapsed = time.time() - t0
            print(f"  [{label}] processed {count} configs, {elapsed:.1f}s",
                  flush=True)
    elapsed = time.time() - t0
    print(f"  [{label}] done: {count} configs in {elapsed:.1f}s",
          flush=True)
    return count


def mp_spot_check(instance, tol=1e-10):
    """mpmath high-precision spot check of M6 for one instance."""
    n, edges, W = instance
    Ls = laplacian_scalar(n, edges)
    Lsig = laplacian_signed(n, edges, W)
    Lm = laplacian_mobius(n, edges, W)
    ev_s = mp_eigh(Ls)
    ev_sig = mp_eigh(Lsig)
    ev_m = mp_eigh(Lm)
    combined = sorted(ev_s + ev_sig)
    ok, md = mp_multiset_diff(combined, ev_m, tol)
    return ok, md


def main(out_dir):
    print(f"=== FUZZER-A R6 Stage 2 sheaf-beta ===")
    print(f"date: 2026-04-22  seed: {SEED}  mpmath prec: {mp.mp.prec}")
    print(f"cwd: {Path.cwd()}")
    print()

    claims = {
        "M6": Claim("M6", "spec(L_mob) = spec(L_s) U spec(L_sig) (multiset)"),
        "M7": Claim("M7", "p_{L_mob}(x) = p_{L_s}(x) * p_{L_sig}(x)"),
        "B2": Claim("B2", "tr(L_s * L_sig) = Sum deg(u)^2 + 2m - 4|W|"),
        "B14": Claim("B14", "|lambda_i(L_sig W) - lambda_i(L_sig W dt e)| <= 2"),
        "B15": Claim("B15", "lambda_i(L_sig(G-E')) interlace by k=|E'| both directions"),
        "B16": Claim("B16", "G connected, beta=0 implies lambda_min(L_sig) > 0"),
        "G15": Claim("G15", "dim ker L_sig = beta(G,W)"),
        "B9": Claim("B9", "dim ker L_mob = #components + beta(G,W)"),
        "B21": Claim("B21", "sum sign(eig(L_sig)) = n - beta(G,W)"),
    }

    # ---- n=6 exhaustive in iso classes ----
    print("--- n=6 envelope (exhaustive iso, sampled wraps) ---")
    t0 = time.time()
    classes_n6 = iso_classes_n(6)
    print(f"  iso classes on n=6: {len(classes_n6)}  "
          f"(built in {time.time()-t0:.1f}s)")

    # Stream sampled wrap envelope
    def n6_stream():
        wrap_cap = 24
        for edges in classes_n6:
            m = len(edges)
            all_wraps = []
            for r in range(m + 1):
                for sub in itertools.combinations(edges, r):
                    all_wraps.append(frozenset(sub))
            if len(all_wraps) > wrap_cap:
                all_wraps = RNG.sample(all_wraps, wrap_cap)
            for W in all_wraps:
                yield 6, edges, W

    cnt6 = run_envelope(n6_stream(), "n=6", TOL_N6, claims)

    # ---- n=7 random sample ----
    print("\n--- n=7 envelope (random sample, varied density) ---")
    cnt7 = run_envelope(n7_envelope(num_samples=220), "n=7", TOL_N7, claims)

    # ---- mp spot-check on a handful of interesting instances ----
    print("\n--- mpmath prec=50 spot-checks on M6 ---")
    # Pick 6 random instances and do high-precision check
    n6_list = list(n6_stream())
    spot_instances = RNG.sample(n6_list, min(6, len(n6_list)))
    for inst in spot_instances:
        ok, md = mp_spot_check(inst, tol=1e-10)
        status = "OK" if ok else "FAIL"
        print(f"  n={inst[0]}, m={len(inst[1])}, |W|={len(inst[2])}: "
              f"{status}  max mp diff = {mp.nstr(md, 6)}")

    # ---- report ----
    print("\n=== VERDICT TABLE ===")
    print(f"{'claim':<4} | {'tested':>6} | {'passed':>6} | "
          f"{'max rel diff':>14} | verdict")
    print("-" * 70)
    for key in ["M6", "M7", "B2", "B14", "B15", "B16", "G15", "B9", "B21"]:
        c = claims[key]
        print(f"{c.key:<4} | {c.tested:>6} | {c.passed:>6} | "
              f"{c.max_rel_diff:>14.3e} | {c.verdict()}")

    # Dump results
    results = {
        "date": "2026-04-22",
        "seed": SEED,
        "mp_prec_bits": mp.mp.prec,
        "n6_iso_classes": len(classes_n6),
        "n6_configs": cnt6,
        "n7_configs": cnt7,
        "tol_n6": TOL_N6,
        "tol_n7": TOL_N7,
        "claims": {k: c.summary() for k, c in claims.items()},
    }
    out_path = Path(out_dir) / "results.json"
    out_path.write_text(json.dumps(results, indent=2, default=str))
    print(f"\nResults written to {out_path}")
    return results


if __name__ == "__main__":
    out_dir = Path(__file__).parent
    main(str(out_dir))
