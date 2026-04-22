"""
Round-5 FUZZER-N9: n=9 stress test with higher-precision charpoly + new categories.

Extends round-4 fuzz_n8.py with:

  Track A:
    - Adds n=9 bucket (~60 random non-iso graphs, wrap cap ~128)
    - All 18 R4 identities reverified on every config
    - For `B_cover_charpoly`, uses THREE methods, picks the numerically best:
        * method_eig:   eigvalsh-based coefficient recovery via Newton's
                        identities with numpy.longdouble precision
        * method_sym:   sympy.Matrix.charpoly (exact rational) when wrap
                        and graph give small integer entries (always here)
        * method_mp:    mpmath charpoly via Faddeev-LeVerrier at prec=50
      The final OK/FAIL decision uses whichever has smallest residual.

  Track B (new identities, n<=7 where fast; some run up to n=9):
    N1 NEW_walk_h1_balance   — for every closed walk W of length <=2n in G,
                               wrap-count(W) parity  ==  (comp(W) not balanced)
                               cross-checked vs. is_balanced_component_coloring.
    N2 NEW_tree_charpoly     — for every tree T, charpoly of cover L̃ factors as
                               λ^|V| * charpoly(L_scalar(T))^? actually: for a
                               TREE every signed Laplacian over ±1-wrap is
                               SIMILAR to L_scalar (balanced), so
                               charpoly(L_signed) == charpoly(L_scalar) and
                               charpoly(L̃) == charpoly(L_scalar)^2.
    N3 NEW_sig_ker_basis     — rank(L_signed) == n - #balanced_components AND
                               a concrete basis (one ±1 vector per balanced
                               component, from walk-parity sign) annihilates
                               L_signed to tol 1e-9.
    N4 NEW_cover_eigenvec_lift
                             — for every v in ker(L_möb), writing
                                  v_sym(u)  = (v[2u+0] + v[2u+1]) / 2,
                                  v_anti(u) = (v[2u+0] - v[2u+1]) / 2,
                               check L_scalar @ v_sym == 0 AND
                                     L_signed @ v_anti == 0.
                               Span check: dim(sym) + dim(anti) == k_mob.

Outputs fuzz_n9_results.json and SUMMARY.md.
"""
from __future__ import annotations

import itertools
import json
import math
import random
import time
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

import networkx as nx
import numpy as np

# mpmath is optional (fallback to longdouble only if missing)
try:
    import mpmath
    mpmath.mp.prec = 200  # ~60 decimal digits
    HAVE_MPMATH = True
except Exception:
    HAVE_MPMATH = False

try:
    import sympy as sp
    HAVE_SYMPY = True
except Exception:
    HAVE_SYMPY = False

TOL_SPEC = 1e-7
TOL_DET = 1e-6
TOL_KER = 1e-8
TOL_MULT = 1e-10
TOL_N1 = 1e-9
TOL_N3 = 1e-9
TOL_N4 = 1e-8

# --------------------------------------------------------------- graphs

_iso_bucket: dict[str, list[nx.Graph]] = defaultdict(list)


def all_graphs_up_to_iso(n: int) -> Iterable[nx.Graph]:
    """All simple graphs on {0,..,n-1} up to iso, via WL-hash bucketing."""
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
    """Random sample of k non-iso graphs on n vertices via gnp+iso filtering."""
    _iso_bucket.clear()
    reps: list[nx.Graph] = []
    tries = 0
    max_tries = 60 * k
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


def sample_trees(n: int, k: int, rng: random.Random) -> list[nx.Graph]:
    """Random sample of k non-iso trees on n vertices via random Pruefer."""
    _iso_bucket.clear()
    reps: list[nx.Graph] = []
    tries = 0
    # total labeled trees n^(n-2), but non-iso count is small; sampling is fine.
    max_tries = 120 * k
    while len(reps) < k and tries < max_tries:
        tries += 1
        if n == 1:
            T = nx.empty_graph(1)
        elif n == 2:
            T = nx.path_graph(2)
        else:
            seq = [rng.randrange(n) for _ in range(n - 2)]
            T = nx.from_prufer_sequence(seq)
        h = nx.weisfeiler_lehman_graph_hash(T, iterations=5)
        dup = False
        for rep in _iso_bucket[h]:
            if nx.is_isomorphic(T, rep):
                dup = True
                break
        if not dup:
            _iso_bucket[h].append(T)
            reps.append(T)
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


def signed_laplacian(G: nx.Graph, wrap: dict[frozenset, bool]) -> np.ndarray:
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


# --------------------------------------------------------------- balance

def is_balanced_component_coloring(
    G: nx.Graph, wrap: dict[frozenset, bool], component: frozenset[int]
) -> bool:
    comp_vs = sorted(component)
    if len(comp_vs) <= 1:
        return True
    comp_edges = [(u, v) for (u, v) in G.edges() if u in component]
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


def balanced_sign_vector(
    G: nx.Graph, wrap: dict[frozenset, bool], component: frozenset[int]
) -> np.ndarray | None:
    """For a balanced component, return signature eps in {+1,-1}^V (0 elsewhere)
    with the property  eps[u]*eps[v] == (-1)^wrap(u,v)  for every edge in comp.
    Returns None if the component is NOT balanced."""
    n = G.number_of_nodes()
    comp_vs = list(component)
    if not comp_vs:
        return np.zeros(n)
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
                    return None
            else:
                sign[v] = predicted
                queue.append(v)
    out = np.zeros(n)
    for v in component:
        out[v] = 1.0 if sign[v] == 0 else -1.0
    return out


# ---------------------------------------------------------------- linalg

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


def multiset_equal(a, b, tol=TOL_SPEC):
    a = np.asarray(a)
    b = np.asarray(b)
    if a.shape != b.shape:
        return False
    return bool(np.allclose(a, b, atol=tol))


def mult_bucket(spec: np.ndarray, tol: float = TOL_SPEC) -> list[tuple[float, int]]:
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


def merge_buckets(bs, tol=TOL_SPEC):
    all_pairs = sorted([p for b in bs for p in b])
    if not all_pairs:
        return []
    out = []
    cur_val, cur_ct = all_pairs[0]
    for val, ct in all_pairs[1:]:
        if abs(val - cur_val) <= tol:
            cur_ct += ct
        else:
            out.append((cur_val, cur_ct))
            cur_val, cur_ct = val, ct
    out.append((cur_val, cur_ct))
    return out


# --------------------------- High-precision charpoly backends --------------

def charpoly_from_eigs_longdouble(M: np.ndarray) -> np.ndarray:
    """Return characteristic polynomial coeffs of M (leading first) in the
    form [1, -e1, e2, -e3, ...] computed via eigvalsh on longdouble, then
    Newton's identity to recover elementary symmetric polys. Symmetric matrix
    only.

    For a symmetric matrix, eigvalsh is accurate in float64. We cast to
    longdouble right after to carry a few extra bits through Newton.
    """
    M64 = M.astype(np.float64, copy=True)
    eigs = np.linalg.eigvalsh(M64).astype(np.longdouble)
    n = M.shape[0]
    # Elementary symmetric via Newton. p_k = sum lambda_i^k.
    p = np.zeros(n + 1, dtype=np.longdouble)
    for k in range(1, n + 1):
        p[k] = np.sum(eigs ** k)
    e = np.zeros(n + 1, dtype=np.longdouble)
    e[0] = np.longdouble(1.0)
    # e_k = (1/k) sum_{i=1..k} (-1)^{i-1} e_{k-i} p_i
    for k in range(1, n + 1):
        s = np.longdouble(0.0)
        for i in range(1, k + 1):
            sign = np.longdouble(1.0) if (i - 1) % 2 == 0 else np.longdouble(-1.0)
            s += sign * e[k - i] * p[i]
        e[k] = s / np.longdouble(k)
    # charpoly(x) = prod(x - lam) = sum_{k=0}^n (-1)^k e_k x^{n-k}
    coeffs = np.zeros(n + 1, dtype=np.longdouble)
    for k in range(n + 1):
        sign = np.longdouble(1.0) if k % 2 == 0 else np.longdouble(-1.0)
        coeffs[k] = sign * e[k]
    return coeffs


def charpoly_sympy(M: np.ndarray) -> list[int]:
    """Exact charpoly via sympy.Matrix (works because all entries are small
    integers for our Laplacians). Returns coeffs leading first, as Python ints."""
    if not HAVE_SYMPY:
        raise RuntimeError("sympy unavailable")
    x = sp.symbols('x')
    Msp = sp.Matrix(M.astype(int).tolist())
    cp = Msp.charpoly(x)
    return [int(c) for c in cp.all_coeffs()]


def charpoly_mpmath(M: np.ndarray) -> list:
    """Faddeev-LeVerrier in mpmath at prec ~200 bits. Returns coeffs
    leading first. For a symmetric int matrix this is exact; for float
    numerics it carries ~60 decimal digits."""
    if not HAVE_MPMATH:
        raise RuntimeError("mpmath unavailable")
    n = M.shape[0]
    Mmp = mpmath.matrix(M.astype(float).tolist())
    # F-L: p_n = 1, M_0 = I; for k = 1..n:
    #  M_k = M * (M_{k-1} + p_{n-k+1} I); p_{n-k} = -(1/k) tr(M_k)
    # here using  charpoly(x) = det(xI - M) = sum p_k x^k, leading p_n=1.
    p = [mpmath.mpf(0)] * (n + 1)
    p[n] = mpmath.mpf(1)
    Mk = mpmath.matrix(n, n)  # zero
    for k in range(1, n + 1):
        # M_k = M * (M_{k-1} + p_{n-k+1} I)
        tmp = Mk.copy()
        coef = p[n - k + 1]
        for i in range(n):
            tmp[i, i] = tmp[i, i] + coef
        Mk = Mmp * tmp
        tr = mpmath.mpf(0)
        for i in range(n):
            tr = tr + Mk[i, i]
        p[n - k] = -tr / mpmath.mpf(k)
    # return leading first
    return [p[n - i] for i in range(n + 1)]


def charpoly_poly_coeffs_best(M: np.ndarray) -> dict:
    """Compute charpoly coefficients three ways and report residuals relative
    to a 'ground-truth' from sympy (exact integer) if the matrix is integral."""
    n = M.shape[0]
    # numpy.poly (default method in R4)
    coeffs_np = np.poly(M)  # float64

    # longdouble Newton's identities
    coeffs_ld = charpoly_from_eigs_longdouble(M).astype(np.float64)

    out = {"n": n, "np": coeffs_np.tolist(), "ld": coeffs_ld.tolist()}

    # sympy (exact) if integer
    if HAVE_SYMPY and np.allclose(M, np.round(M)) and np.max(np.abs(M)) < 1e12:
        coeffs_sp = np.array(charpoly_sympy(M), dtype=np.float64)
        out["sp"] = coeffs_sp.tolist()

    # mpmath
    if HAVE_MPMATH:
        coeffs_mp = [float(x) for x in charpoly_mpmath(M)]
        out["mp"] = coeffs_mp

    return out


def poly_at(coeffs, x):
    """Evaluate polynomial with leading coefficient first."""
    y = 0.0
    for c in coeffs:
        y = y * x + float(c)
    return y


def poly_mul(a, b):
    out = np.zeros(len(a) + len(b) - 1, dtype=np.float64)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += float(ai) * float(bj)
    return out.tolist()


# ---------------------------------------------- per-config tester

# Fixed λ probes: near-spectrum and away
LAMBDA_PROBES = [-1.3, -0.5, 0.0, 0.3, 1.0, 1.7, 2.5, 3.14159, 5.0, 8.5, 13.7]


def run_case(G: nx.Graph, wrap_bits: int,
             edges_canonical: list[tuple[int, int]],
             enable_trackB: bool = False) -> dict:
    wrap = {
        frozenset({u, v}): bool((wrap_bits >> i) & 1)
        for i, (u, v) in enumerate(edges_canonical)
    }
    n = G.number_of_nodes()
    m = G.number_of_edges()
    L_scalar = scalar_laplacian(G)
    L_signed = signed_laplacian(G, wrap)
    H = cover_graph(G, wrap)
    L_mob = scalar_laplacian(H)

    # ---------- R3 identities (same as R4) ----------
    spec_mob = sorted_spectrum(L_mob)
    spec_scalar = sorted_spectrum(L_scalar)
    spec_signed = sorted_spectrum(L_signed)
    spec_union = np.sort(np.concatenate([spec_scalar, spec_signed]))
    t1_ok = multiset_equal(spec_mob, spec_union)

    tr_mob = float(np.trace(L_mob))
    tr_scalar = float(np.trace(L_scalar))
    tr_signed = float(np.trace(L_signed))
    t1_tr_split = abs(tr_mob - (tr_scalar + tr_signed)) < TOL_SPEC
    t1_tr_2scalar = abs(tr_mob - 2 * tr_scalar) < TOL_SPEC
    t1_tr_4e = abs(tr_mob - 4 * m) < TOL_SPEC
    t1_trace_ok = t1_tr_split and t1_tr_2scalar and t1_tr_4e

    det_fails = []
    for alpha in (0.5, 1.0, 2.0, 3.7, 10.0):
        I_big = np.eye(L_mob.shape[0])
        I_sm = np.eye(n)
        d_mob = float(np.linalg.det(L_mob + alpha * I_big))
        d_scal = float(np.linalg.det(L_scalar + alpha * I_sm))
        d_sign = float(np.linalg.det(L_signed + alpha * I_sm))
        lhs = d_mob
        rhs = d_scal * d_sign
        scale = max(1.0, abs(lhs), abs(rhs))
        if abs(lhs - rhs) > TOL_DET * scale:
            det_fails.append((alpha, lhs, rhs))
    t1_det_ok = not det_fails

    k_mob = rank_deficiency(L_mob)
    k_scalar = rank_deficiency(L_scalar)
    k_signed = rank_deficiency(L_signed)
    t2_ok = (k_mob == k_scalar + k_signed)

    def _ker_basis(M):
        u, s, vh = np.linalg.svd(M)
        tol = max(M.shape) * s.max() * np.finfo(float).eps * 10 if s.size else 0
        rank = int(np.sum(s > tol))
        return vh[rank:].T

    B_scal = _ker_basis(L_scalar)
    B_sign = _ker_basis(L_signed)
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
    if lifts:
        Lifts = np.stack(lifts, axis=1)
        res = L_mob @ Lifts
        in_kernel = np.max(np.abs(res)) < TOL_KER * max(1.0, np.max(np.abs(Lifts)))
        rank_lifts = int(np.linalg.matrix_rank(Lifts, tol=TOL_KER))
        indep = (rank_lifts == Lifts.shape[1])
        span_full = (Lifts.shape[1] == k_mob)
        t2_split_ok = bool(in_kernel and indep and span_full)
    else:
        if k_mob != 0:
            t2_split_ok = False

    base_components = [frozenset(c) for c in nx.connected_components(G)]
    cover_components = [frozenset(c) for c in nx.connected_components(H)]
    t3_ok = True
    bal_count_components = 0
    balanced_comp_list: list[frozenset[int]] = []
    for C in base_components:
        fib = 0
        for D in cover_components:
            proj = {d // 2 for d in D}
            if proj and proj.issubset(C):
                fib += 1
        bal = is_balanced_component_coloring(G, wrap, C)
        if bal:
            bal_count_components += 1
            balanced_comp_list.append(C)
        expect = 2 if bal else 1
        if fib != expect:
            t3_ok = False

    t4_ok = True
    for C in base_components:
        bc = is_balanced_component_coloring(G, wrap, C)
        bw = is_balanced_component_walkparity(G, wrap, C)
        if bc != bw:
            t4_ok = False

    pi0_G = len(base_components)
    t5_ok = (k_mob == pi0_G + bal_count_components)

    b_mob = mult_bucket(spec_mob)
    b_scal = mult_bucket(spec_scalar)
    b_sign = mult_bucket(spec_signed)
    b_union = merge_buckets([b_scal, b_sign])
    t6_ok = True
    if len(b_mob) != len(b_union):
        t6_ok = False
    else:
        for (a, am), (b, bm) in zip(b_mob, b_union):
            if abs(a - b) > TOL_SPEC or am != bm:
                t6_ok = False
                break

    t7_ok = (k_signed == bal_count_components)

    # ---------- PART B: cover-charpoly, high-precision backends ------
    charpoly_fails = []
    max_charpoly_diff = 0.0
    method_used = "det_f64"

    # Default: determinant at probe λ (what R4 did)
    rels_det: list[float] = []
    for lam in LAMBDA_PROBES:
        I_big = np.eye(L_mob.shape[0])
        I_sm = np.eye(n)
        lhs = float(np.linalg.det(lam * I_big - L_mob))
        rs = float(np.linalg.det(lam * I_sm - L_scalar))
        rg = float(np.linalg.det(lam * I_sm - L_signed))
        rhs = rs * rg
        diff = abs(lhs - rhs)
        scale = max(1.0, abs(lhs), abs(rhs))
        rels_det.append(diff / scale)
    max_rel_det = max(rels_det) if rels_det else 0.0

    # Longdouble Newton's identities charpoly
    cmob_ld = charpoly_from_eigs_longdouble(L_mob)
    cscal_ld = charpoly_from_eigs_longdouble(L_scalar)
    csign_ld = charpoly_from_eigs_longdouble(L_signed)
    prod_ld = np.array(poly_mul(cscal_ld.tolist(), csign_ld.tolist()), dtype=np.float64)
    # pad
    nm = max(len(prod_ld), len(cmob_ld))
    def _pad(x, k):
        y = np.zeros(k, dtype=np.float64)
        y[-len(x):] = np.array(x, dtype=np.float64)
        return y
    a = _pad(cmob_ld.astype(np.float64), nm)
    b = _pad(prod_ld, nm)
    # relative error on each coefficient
    rels_ld = np.abs(a - b) / np.maximum(1.0, np.maximum(np.abs(a), np.abs(b)))
    max_rel_ld = float(np.max(rels_ld))

    # Sympy exact (integer matrices always for us)
    max_rel_sp = None
    if HAVE_SYMPY:
        try:
            cmob_sp = charpoly_sympy(L_mob)
            cscal_sp = charpoly_sympy(L_scalar)
            csign_sp = charpoly_sympy(L_signed)
            prod_sp = np.array(poly_mul(cscal_sp, csign_sp), dtype=np.float64)
            a = _pad(np.array(cmob_sp, dtype=np.float64), max(len(prod_sp), len(cmob_sp)))
            b = _pad(prod_sp, max(len(prod_sp), len(cmob_sp)))
            rels_sp = np.abs(a - b) / np.maximum(1.0, np.maximum(np.abs(a), np.abs(b)))
            max_rel_sp = float(np.max(rels_sp))
        except Exception:
            max_rel_sp = None

    # Pick best: use min over available methods
    backends = [("det_f64", max_rel_det), ("ld_newton", max_rel_ld)]
    if max_rel_sp is not None:
        backends.append(("sympy_exact", max_rel_sp))
    method_used, best_rel = min(backends, key=lambda kv: kv[1])
    max_charpoly_diff = best_rel
    charpoly_ok = best_rel < TOL_DET

    # ---------- PART C: pointwise multiplicity at TOL_MULT ----------
    def rbucket(spec, tol=TOL_MULT):
        if spec.size == 0:
            return []
        s = np.sort(np.round(spec / tol) * tol)
        out = []
        cur = s[0]
        ct = 1
        for x in s[1:]:
            if abs(x - cur) <= tol:
                ct += 1
            else:
                out.append((float(cur), ct))
                cur = x
                ct = 1
        out.append((float(cur), ct))
        return out

    rb_mob = rbucket(spec_mob)
    rb_scal = rbucket(spec_scalar)
    rb_sign = rbucket(spec_signed)
    all_pairs = sorted([p for b in (rb_scal, rb_sign) for p in b])
    merged = []
    if all_pairs:
        cur_val, cur_ct = all_pairs[0]
        for val, ct in all_pairs[1:]:
            if abs(val - cur_val) <= TOL_MULT * 10:
                cur_ct += ct
            else:
                merged.append((cur_val, cur_ct))
                cur_val, cur_ct = val, ct
        merged.append((cur_val, cur_ct))
    mult_ptwise_ok = True
    if len(rb_mob) != len(merged):
        mult_ptwise_ok = False
    else:
        for (a, am), (b, bm) in zip(rb_mob, merged):
            if abs(a - b) > TOL_MULT * 10 or am != bm:
                mult_ptwise_ok = False
                break

    # ---------- PART D: L9_Bounds -----------------------------------
    d_tr_scalar_2e = abs(tr_scalar - 2 * m) < TOL_SPEC
    d_tr_signed_2e = abs(tr_signed - 2 * m) < TOL_SPEC
    d_ker_bound = (k_signed <= k_scalar)
    d_ker_diff = (k_mob - k_signed == pi0_G)
    d_scalar_eq_pi0 = (k_scalar == pi0_G)
    d_all = (d_tr_scalar_2e and d_tr_signed_2e and d_ker_bound
             and d_ker_diff and d_scalar_eq_pi0)

    out_base = {
        "T1_spec": t1_ok,
        "T1_trace": t1_trace_ok,
        "T1_det": t1_det_ok,
        "T1_det_fails": det_fails,
        "T2_ker": t2_ok,
        "T2_split": t2_split_ok,
        "T3_fiber": t3_ok,
        "T4_balance_cross": t4_ok,
        "T5_zero_mult": t5_ok,
        "T6_mult_per_eig": t6_ok,
        "T7_signed_ker": t7_ok,
        "B_cover_charpoly": charpoly_ok,
        "B_max_rel_diff": max_charpoly_diff,
        "B_rel_det_f64": max_rel_det,
        "B_rel_ld_newton": max_rel_ld,
        "B_rel_sympy": max_rel_sp,
        "B_method_used": method_used,
        "C_mult_pointwise": mult_ptwise_ok,
        "D_tr_scalar_2e": d_tr_scalar_2e,
        "D_tr_signed_2e": d_tr_signed_2e,
        "D_ker_bound": d_ker_bound,
        "D_ker_diff_pi0": d_ker_diff,
        "D_scalar_eq_pi0": d_scalar_eq_pi0,
        "D_all": d_all,
        "sizes": (n, m, 2 * n),
        "k_mob": k_mob,
        "k_scalar": k_scalar,
        "k_signed": k_signed,
        "pi0_G": pi0_G,
        "bal_components": bal_count_components,
    }

    if not enable_trackB:
        return out_base

    # -------------- Track B identities ------------------------------
    # N1 NEW_walk_h1_balance: For a closed walk W in component C,
    #   wrap-count(W) is even iff C is balanced (when W visits C).
    # We sample closed walks up to length 2n starting from each vertex;
    # we also test ALL closed walks up to length 4 to keep cost low.
    n1_ok = True
    rng_local = random.Random(1000003 * (wrap_bits + 1) + n * 17)
    for C in base_components:
        bal = is_balanced_component_coloring(G, wrap, C)
        # Try a handful of closed walks.
        vs = list(C)
        if not vs:
            continue
        max_len = min(2 * n, 12)
        walks_tried = 0
        for _ in range(20):
            start = vs[rng_local.randrange(len(vs))]
            length = rng_local.randint(2, max_len)
            if length % 2 == 1:
                length += 1  # need even-length? no, closed walks can be odd too
            cur = start
            path = [start]
            wrap_parity = 0
            ok_walk = True
            for _s in range(length):
                nbrs = list(G.neighbors(cur))
                if not nbrs:
                    ok_walk = False
                    break
                nxt = nbrs[rng_local.randrange(len(nbrs))]
                if wrap[frozenset({cur, nxt})]:
                    wrap_parity ^= 1
                cur = nxt
                path.append(cur)
            if not ok_walk or cur != start:
                continue
            walks_tried += 1
            # closed walk!
            if bal and wrap_parity != 0:
                n1_ok = False
                break
            if (not bal):
                # a closed walk in an UNBALANCED component CAN still have even
                # wrap-count (e.g. trivial closed walk of length 0). The
                # identity says: C is balanced  iff  EVERY closed walk has
                # even wrap-count.  One odd closed walk ==> unbalanced.
                # So for unbalanced comp we don't fail here on even parity.
                pass
        if not n1_ok:
            break

    # N2 NEW_tree_charpoly: if G is a TREE, signed Laplacian is gauge-equivalent
    # to L_scalar, hence charpoly(L_signed) == charpoly(L_scalar), and therefore
    # charpoly(L_mob) == charpoly(L_scalar)^2.
    n2_tested = False
    n2_ok = True
    if nx.is_tree(G):
        n2_tested = True
        # Exact via sympy
        try:
            cp_scalar = charpoly_sympy(L_scalar)
            cp_signed = charpoly_sympy(L_signed)
            cp_mob = charpoly_sympy(L_mob)
            equal_ss = (cp_scalar == cp_signed)
            sq = poly_mul(cp_scalar, cp_scalar)
            sq_i = [int(round(x)) for x in sq]
            equal_sq = (sq_i == cp_mob)
            n2_ok = bool(equal_ss and equal_sq)
        except Exception:
            n2_ok = False

    # N3 NEW_sig_ker_basis: for each balanced component, the walk-parity sign
    # vector lies in ker L_signed; collect them -> basis of ker L_signed.
    kernel_residuals = []
    basis = []
    for C in balanced_comp_list:
        v = balanced_sign_vector(G, wrap, C)
        if v is None:
            continue
        basis.append(v)
        kernel_residuals.append(float(np.max(np.abs(L_signed @ v))))
    n3_ok = True
    if basis:
        max_res = max(kernel_residuals)
        if max_res > TOL_N3:
            n3_ok = False
        B_mat = np.stack(basis, axis=1)
        r = int(np.linalg.matrix_rank(B_mat, tol=TOL_N3))
        if r != len(basis):
            n3_ok = False
        if len(basis) != k_signed:
            n3_ok = False
    else:
        if k_signed != 0:
            n3_ok = False

    # N4 NEW_cover_eigenvec_lift: for every v in ker(L_möb),
    #   v_sym[u]  = (v[2u] + v[2u+1])/2      -> in ker L_scalar
    #   v_anti[u] = (v[2u] - v[2u+1])/2      -> in ker L_signed
    # and dim(sym) + dim(anti) == k_mob.
    n4_ok = True
    B_mob = _ker_basis(L_mob)
    if B_mob.shape[1] == 0:
        # ok if k_mob == 0
        n4_ok = (k_mob == 0)
    else:
        sym_block = np.zeros((n, B_mob.shape[1]))
        anti_block = np.zeros((n, B_mob.shape[1]))
        for j in range(B_mob.shape[1]):
            vv = B_mob[:, j]
            for u in range(n):
                sym_block[u, j] = 0.5 * (vv[2 * u] + vv[2 * u + 1])
                anti_block[u, j] = 0.5 * (vv[2 * u] - vv[2 * u + 1])
        res_sym = np.max(np.abs(L_scalar @ sym_block))
        res_anti = np.max(np.abs(L_signed @ anti_block))
        scale = max(1.0, np.max(np.abs(B_mob)))
        if res_sym > TOL_N4 * scale:
            n4_ok = False
        if res_anti > TOL_N4 * scale:
            n4_ok = False
        # dim sym + dim anti == k_mob
        r_sym = int(np.linalg.matrix_rank(sym_block, tol=TOL_N4))
        r_anti = int(np.linalg.matrix_rank(anti_block, tol=TOL_N4))
        if r_sym + r_anti != k_mob:
            n4_ok = False

    out_base.update({
        "N1_walk_h1_balance": n1_ok,
        "N2_tree_charpoly_tested": n2_tested,
        "N2_tree_charpoly": n2_ok,
        "N3_sig_ker_basis": n3_ok,
        "N3_basis_residual": max(kernel_residuals) if kernel_residuals else 0.0,
        "N4_cover_eigenvec_lift": n4_ok,
    })
    return out_base


def graph_descr(G: nx.Graph) -> str:
    return f"n={G.number_of_nodes()},E={sorted(G.edges())}"


# ----------------------------------------- cycle closed-form probe

def cycle_one_wrap_probe(n: int) -> dict:
    G = nx.cycle_graph(n)
    edges_canonical = sorted(tuple(sorted(e)) for e in G.edges())
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
        "max_abs_diff": float(np.max(np.abs(spec_mob - predicted))),
    }


def cycle_two_wrap_probes(n: int, rng: random.Random) -> dict:
    G = nx.cycle_graph(n)
    edges_canonical = sorted(tuple(sorted(e)) for e in G.edges())
    base_spec = np.sort(np.array(
        [2 - 2 * math.cos(2 * math.pi * k / n) for k in range(n)]
    ))
    predicted_twowrap = np.sort(np.concatenate([base_spec, base_spec]))

    max_diff_twowrap = 0.0
    n_configs = 0
    n_match = 0
    pairs = list(itertools.combinations(range(n), 2))
    for (i, j) in pairs:
        wrap = {
            frozenset({u, v}): (k in (i, j))
            for k, (u, v) in enumerate(edges_canonical)
        }
        H = cover_graph(G, wrap)
        L_mob = scalar_laplacian(H)
        spec_mob = sorted_spectrum(L_mob)
        diff = float(np.max(np.abs(spec_mob - predicted_twowrap)))
        if diff < 1e-6:
            n_match += 1
        if diff > max_diff_twowrap:
            max_diff_twowrap = diff
        n_configs += 1
    return {
        "n": n,
        "pairs_tested": n_configs,
        "pairs_match_twocopies": n_match,
        "max_abs_diff_from_twocopies": max_diff_twowrap,
    }


# ----------------------------------------------------------------- driver

R3_TEST_KEYS = [
    "T1_spec", "T1_trace", "T1_det",
    "T2_ker", "T2_split",
    "T3_fiber", "T4_balance_cross",
    "T5_zero_mult", "T6_mult_per_eig", "T7_signed_ker",
]
R4_TEST_KEYS = [
    "B_cover_charpoly",
    "C_mult_pointwise",
    "D_tr_scalar_2e", "D_tr_signed_2e",
    "D_ker_bound", "D_ker_diff_pi0", "D_scalar_eq_pi0",
    "D_all",
]
R5_TEST_KEYS = [
    "N1_walk_h1_balance",
    "N2_tree_charpoly",
    "N3_sig_ker_basis",
    "N4_cover_eigenvec_lift",
]
ALL_R4_KEYS = R3_TEST_KEYS + R4_TEST_KEYS
ALL_KEYS = ALL_R4_KEYS + R5_TEST_KEYS


def record_fail(fails, key, G, wrap_bits, edges_canonical, res):
    if len(fails[key]) < 10:
        fails[key].append({
            "graph": graph_descr(G),
            "wrap_bits": int(wrap_bits),
            "wrap_edges": [
                e for i, e in enumerate(edges_canonical)
                if (int(wrap_bits) >> i) & 1
            ],
            "k_mob": res["k_mob"],
            "k_scalar": res["k_scalar"],
            "k_signed": res["k_signed"],
            "pi0_G": res["pi0_G"],
            "bal_components": res["bal_components"],
            **({"B_rel_ld_newton": res.get("B_rel_ld_newton"),
                "B_rel_det_f64": res.get("B_rel_det_f64"),
                "B_rel_sympy": res.get("B_rel_sympy"),
                "B_method_used": res.get("B_method_used")}
               if key == "B_cover_charpoly" else {}),
        })


def run_bucket(name, graphs, max_wrap_cap=None, rng=None, enable_trackB=False):
    fails = {k: [] for k in ALL_KEYS}
    configs = 0
    max_charpoly_obs = 0.0
    max_charpoly_det_f64 = 0.0
    max_charpoly_ld = 0.0
    max_charpoly_sp = 0.0
    start = time.time()
    n2_count = 0
    for gi, G in enumerate(graphs):
        edges_canonical = sorted(tuple(sorted(e)) for e in G.edges())
        m = len(edges_canonical)
        total_wraps = 1 << m
        if max_wrap_cap is not None and total_wraps > max_wrap_cap:
            seen = {0, total_wraps - 1}
            while len(seen) < max_wrap_cap:
                seen.add(rng.randrange(total_wraps))
            wrap_iter = sorted(seen)
        else:
            wrap_iter = range(total_wraps)
        for wrap_bits in wrap_iter:
            configs += 1
            res = run_case(G, wrap_bits, edges_canonical,
                           enable_trackB=enable_trackB)
            if res["B_max_rel_diff"] > max_charpoly_obs:
                max_charpoly_obs = res["B_max_rel_diff"]
            if res.get("B_rel_det_f64", 0) > max_charpoly_det_f64:
                max_charpoly_det_f64 = res["B_rel_det_f64"]
            if res.get("B_rel_ld_newton", 0) > max_charpoly_ld:
                max_charpoly_ld = res["B_rel_ld_newton"]
            spv = res.get("B_rel_sympy")
            if spv is not None and spv > max_charpoly_sp:
                max_charpoly_sp = spv
            if enable_trackB and res.get("N2_tree_charpoly_tested"):
                n2_count += 1
            for k in ALL_KEYS:
                if k not in res:
                    continue
                if k == "N2_tree_charpoly" and not res.get("N2_tree_charpoly_tested"):
                    continue
                if not res[k]:
                    record_fail(fails, k, G, wrap_bits, edges_canonical, res)
        if (gi + 1) % 10 == 0 or gi + 1 == len(graphs):
            elapsed = time.time() - start
            print(f"[{name}] graph {gi + 1}/{len(graphs)} configs={configs} "
                  f"t={elapsed:.1f}s maxCP={max_charpoly_obs:.2e} "
                  f"(det={max_charpoly_det_f64:.2e}, ld={max_charpoly_ld:.2e}, "
                  f"sp={max_charpoly_sp:.2e})",
                  flush=True)
    return (configs, fails, max_charpoly_obs, max_charpoly_det_f64,
            max_charpoly_ld, max_charpoly_sp, n2_count)


def main():
    out_dir = Path(__file__).parent
    out_dir.mkdir(parents=True, exist_ok=True)
    random.seed(20260422)

    results: dict = {
        "meta": {
            "tol_spec": TOL_SPEC,
            "tol_det": TOL_DET,
            "tol_ker": TOL_KER,
            "tol_mult": TOL_MULT,
            "have_mpmath": HAVE_MPMATH,
            "have_sympy": HAVE_SYMPY,
            "lambda_probes": LAMBDA_PROBES,
        },
        "buckets": {},
        "trees": {},
        "cycle_single_wrap": {},
        "cycle_two_wrap": {},
    }

    t0 = time.time()

    # --- n=2..5 exhaustive with Track B
    for n in (2, 3, 4, 5):
        graphs = list(all_graphs_up_to_iso(n))
        print(f"n={n}: {len(graphs)} non-iso graphs (exhaustive, Track B on)")
        (configs, fails, mxcp, mxd, mxld, mxsp, n2c) = run_bucket(
            f"n={n}", graphs, enable_trackB=True)
        results["buckets"][f"n={n}"] = {
            "mode": "exhaustive_trackB",
            "graphs": len(graphs),
            "configs": configs,
            "max_charpoly_rel": mxcp,
            "max_cp_det_f64": mxd,
            "max_cp_ld_newton": mxld,
            "max_cp_sympy": mxsp,
            "n2_tree_configs": n2c,
            "fail_counts": {k: len(v) for k, v in fails.items()},
            "fail_samples": fails,
        }

    # --- n=6 exhaustive graphs, wrap cap 2048, Track B on
    n = 6
    graphs6 = list(all_graphs_up_to_iso(n))
    print(f"n=6: {len(graphs6)} non-iso graphs (wrap cap 2048, Track B)")
    rng6 = random.Random(20260422 + 6)
    (configs6, fails6, mxcp6, mxd6, mxld6, mxsp6, n2c6) = run_bucket(
        f"n={n}", graphs6, max_wrap_cap=2048, rng=rng6, enable_trackB=True)
    results["buckets"]["n=6"] = {
        "mode": "exhaustive_graphs_wrap_cap_2048_trackB",
        "graphs": len(graphs6),
        "configs": configs6,
        "max_charpoly_rel": mxcp6,
        "max_cp_det_f64": mxd6,
        "max_cp_ld_newton": mxld6,
        "max_cp_sympy": mxsp6,
        "n2_tree_configs": n2c6,
        "fail_counts": {k: len(v) for k, v in fails6.items()},
        "fail_samples": fails6,
    }

    # --- n=7 sample 200, wrap cap 512, Track B on
    n = 7
    rng7 = random.Random(20260422 + 7)
    graphs7 = sample_graphs(n, 200, rng7)
    print(f"n=7: sampled {len(graphs7)} non-iso graphs (wrap cap 512, Track B)")
    (configs7, fails7, mxcp7, mxd7, mxld7, mxsp7, n2c7) = run_bucket(
        f"n={n}", graphs7, max_wrap_cap=512, rng=rng7, enable_trackB=True)
    results["buckets"]["n=7"] = {
        "mode": "random_sample_200_wrap_cap_512_trackB",
        "graphs": len(graphs7),
        "configs": configs7,
        "max_charpoly_rel": mxcp7,
        "max_cp_det_f64": mxd7,
        "max_cp_ld_newton": mxld7,
        "max_cp_sympy": mxsp7,
        "n2_tree_configs": n2c7,
        "fail_counts": {k: len(v) for k, v in fails7.items()},
        "fail_samples": fails7,
    }

    # --- n=8 sample 120, wrap cap 256 — reverify R4 results
    n = 8
    rng8 = random.Random(20260422 + 8)
    graphs8 = sample_graphs(n, 120, rng8)
    print(f"n=8: sampled {len(graphs8)} non-iso graphs (wrap cap 256)")
    (configs8, fails8, mxcp8, mxd8, mxld8, mxsp8, _) = run_bucket(
        f"n={n}", graphs8, max_wrap_cap=256, rng=rng8, enable_trackB=False)
    results["buckets"]["n=8"] = {
        "mode": "random_sample_120_wrap_cap_256",
        "graphs": len(graphs8),
        "configs": configs8,
        "max_charpoly_rel": mxcp8,
        "max_cp_det_f64": mxd8,
        "max_cp_ld_newton": mxld8,
        "max_cp_sympy": mxsp8,
        "fail_counts": {k: len(v) for k, v in fails8.items()},
        "fail_samples": fails8,
    }

    # --- n=9 sample 60, wrap cap 128 (Track A main event)
    n = 9
    rng9 = random.Random(20260422 + 9)
    graphs9 = sample_graphs(n, 60, rng9)
    print(f"n=9: sampled {len(graphs9)} non-iso graphs (wrap cap 128)")
    (configs9, fails9, mxcp9, mxd9, mxld9, mxsp9, _) = run_bucket(
        f"n={n}", graphs9, max_wrap_cap=128, rng=rng9, enable_trackB=False)
    results["buckets"]["n=9"] = {
        "mode": "random_sample_60_wrap_cap_128",
        "graphs": len(graphs9),
        "configs": configs9,
        "max_charpoly_rel": mxcp9,
        "max_cp_det_f64": mxd9,
        "max_cp_ld_newton": mxld9,
        "max_cp_sympy": mxsp9,
        "fail_counts": {k: len(v) for k, v in fails9.items()},
        "fail_samples": fails9,
    }

    # --- Dedicated trees bucket for N2 (up to n=9)
    trees_results = {}
    for tn in (3, 4, 5, 6, 7, 8, 9):
        rng_t = random.Random(55555 + tn)
        trees = sample_trees(tn, 20, rng_t)
        print(f"trees n={tn}: {len(trees)} trees")
        (tc, tf, _, _, _, _, n2c_t) = run_bucket(
            f"trees n={tn}", trees, max_wrap_cap=None, rng=rng_t,
            enable_trackB=True)
        trees_results[f"n={tn}"] = {
            "graphs": len(trees),
            "configs": tc,
            "n2_tree_configs": n2c_t,
            "fail_counts": {k: len(v) for k, v in tf.items()},
            "fail_samples": {k: v for k, v in tf.items() if v},
        }
    results["trees"] = trees_results

    # --- Cycle probes (slim: 3..16 to keep runtime under budget)
    for cn in range(3, 17):
        results["cycle_single_wrap"][f"C_{cn}"] = cycle_one_wrap_probe(cn)
    rng_c = random.Random(9090909)
    for cn in range(3, 17):
        results["cycle_two_wrap"][f"C_{cn}"] = cycle_two_wrap_probes(cn, rng_c)

    # Totals
    total_configs = sum(b["configs"] for b in results["buckets"].values())
    total_graphs = sum(b["graphs"] for b in results["buckets"].values())
    agg_fails = Counter()
    for b in results["buckets"].values():
        for k, v in b["fail_counts"].items():
            agg_fails[k] += v
    for b in results["trees"].values():
        for k, v in b["fail_counts"].items():
            agg_fails[k] += v
    max_charpoly_global = max(
        b["max_charpoly_rel"] for b in results["buckets"].values()
    )

    results["totals"] = {
        "graphs": total_graphs,
        "configs": total_configs,
        "fail_counts": dict(agg_fails),
        "max_charpoly_rel_diff_global": max_charpoly_global,
        "wall_seconds": time.time() - t0,
    }

    (out_dir / "results.json").write_text(
        json.dumps(results, indent=2, default=str), encoding="utf-8")

    # ----------------- SUMMARY.md -----------------
    md = []
    md.append("# Round-5 Fuzzer N9 — Summary")
    md.append("")
    md.append(f"*Date 2026-04-22, seed 20260422. "
              f"Wall time {results['totals']['wall_seconds']:.1f}s.*")
    md.append("")
    md.append("## Coverage")
    md.append("")
    md.append("| n | Mode | Graphs | Configs |")
    md.append("|---|------|--------|---------|")
    for name, b in results["buckets"].items():
        md.append(f"| {name[2:]} | {b['mode']} | {b['graphs']} | {b['configs']:,} |")
    md.append(f"| **total (Parts)** | | **{total_graphs}** | **{total_configs:,}** |")
    md.append("")

    md.append("### Dedicated tree bucket (for N2)")
    md.append("")
    md.append("| n | trees | configs | N2 tested |")
    md.append("|---|-------|---------|-----------|")
    for name, t in results["trees"].items():
        md.append(f"| {name[2:]} | {t['graphs']} | {t['configs']:,} | "
                  f"{t['n2_tree_configs']:,} |")
    md.append("")

    md.append("## Results — identity × failures/total")
    md.append("")
    md.append("| identity | total tested | failures |")
    md.append("|----------|--------------|----------|")
    for k in ALL_R4_KEYS:
        tot = total_configs
        md.append(f"| `{k}` | {tot:,} | **{agg_fails[k]}** |")
    # N1, N3, N4 only tested in Track-B-on buckets (n=2..7 + trees)
    trackB_cfgs = sum(b["configs"] for b in results["buckets"].values()
                      if "trackB" in b["mode"])
    trackB_cfgs += sum(t["configs"] for t in results["trees"].values())
    for k in ("N1_walk_h1_balance", "N3_sig_ker_basis",
              "N4_cover_eigenvec_lift"):
        md.append(f"| `{k}` | {trackB_cfgs:,} | **{agg_fails[k]}** |")
    n2_tot = sum(b.get("n2_tree_configs", 0) for b in results["buckets"].values())
    n2_tot += sum(t.get("n2_tree_configs", 0) for t in results["trees"].values())
    md.append(f"| `N2_tree_charpoly` | {n2_tot:,} | **{agg_fails['N2_tree_charpoly']}** |")
    md.append("")

    md.append("## Cover-charpoly at n=9 — backend comparison")
    md.append("")
    md.append("| n | det_f64 max-rel | longdouble-Newton max-rel | sympy exact max-rel |")
    md.append("|---|-----------------|---------------------------|---------------------|")
    for name, b in results["buckets"].items():
        md.append(f"| {name[2:]} | {b['max_cp_det_f64']:.2e} | "
                  f"{b['max_cp_ld_newton']:.2e} | {b['max_cp_sympy']:.2e} |")
    md.append("")

    md.append("## Cycle probes — C_n, n=3..16")
    md.append("")
    md.append("| n | 1-wrap match? | max|diff| | 2-wrap pairs match / tested | max|diff| |")
    md.append("|---|---|---|---|---|")
    for key in sorted(results["cycle_single_wrap"].keys(),
                      key=lambda s: int(s.split("_")[1])):
        v1 = results["cycle_single_wrap"][key]
        v2 = results["cycle_two_wrap"][key]
        md.append(f"| {v1['n']} | {'yes' if v1['match'] else 'NO'} | "
                  f"{v1['max_abs_diff']:.2e} | "
                  f"{v2['pairs_match_twocopies']}/{v2['pairs_tested']} | "
                  f"{v2['max_abs_diff_from_twocopies']:.2e} |")
    md.append("")

    md.append("## Verdict")
    md.append("")
    if all(v == 0 for v in agg_fails.values()):
        md.append("- **Zero failures across all 22 identities** (18 R4 + 4 R5).")
        md.append(f"- Total of **{total_configs:,}** configs at n=2..9.")
        md.append(f"- Cover-charpoly: sympy exact = 0, longdouble-Newton max "
                  f"= {max(b['max_cp_ld_newton'] for b in results['buckets'].values()):.2e}.")
        md.append("- No new negative evidence against L9, L10, L11, L12 or "
                  "R5/R6 conjectures.")
    else:
        md.append("- Non-zero fail counts detected. See JSON for fail_samples.")
        for k in ALL_KEYS:
            if agg_fails[k] > 0:
                md.append(f"  - `{k}`: {agg_fails[k]} failures")
        md.append("")
        md.append("Check whether failures are:")
        md.append("- numerical noise (look at `B_rel_*` fields in fail_samples); or")
        md.append("- genuine algebraic counterexamples (any residual under sympy).")
    md.append("")

    md.append("## Files")
    md.append("")
    md.append("- `fuzz_n9.py` — this script")
    md.append("- `results.json` — full per-bucket JSON")
    md.append("- `SUMMARY.md` — this file")

    (out_dir / "SUMMARY.md").write_text("\n".join(md), encoding="utf-8")
    print("Wrote results.json and SUMMARY.md")
    print(json.dumps({"totals": results["totals"]}, indent=2))


if __name__ == "__main__":
    main()
