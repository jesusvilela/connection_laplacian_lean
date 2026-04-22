"""
NEGATOR-B R6 Stage 5 - second-wave claim discovery.

Fuzzes ~17 NEW candidate theorems that are orthogonal to everything fuzzed
or landed in stages 1-4. Directions:
  1. M6/M7 corollaries (trace-power, heat, zeta, resolvent, charpoly)
  2. Contraction-Lipschitz |dbeta| bounds (not one-sided, since those failed)
  3. gamma-beta bilinear trace forms
  4. Graph operations / products
  5. Refined one-sided monotonicities (complement of A8, triangle-closing,
     bridge-wrap-flip)

Pure Python + networkx + numpy + mpmath. Seed 20260430.
Envelope: n<=5 exhaustive + n=6 sample ~300 configs/claim.
Budget: ~15 min wall.
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
import networkx as nx

try:
    import mpmath as mp
    mp.mp.prec = 50
    HAVE_MP = True
except Exception:
    HAVE_MP = False


SEED = 20260430
RNG = random.Random(SEED)
np.random.seed(SEED & 0xFFFFFFFF)


# ---------------------------------------------------------------------------
# Primitives
# ---------------------------------------------------------------------------

def edges_from_mask(n, mask):
    potential = list(itertools.combinations(range(n), 2))
    return [potential[i] for i in range(len(potential)) if (mask >> i) & 1]


def degrees(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return deg


def connected_components(n, edges):
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
    """Number of balanced connected components."""
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


def is_bridge(n, edges, e):
    """Is edge e a bridge (removing it increases component count)?"""
    before = num_components(n, edges)
    edges2 = [x for x in edges if x != e]
    after = num_components(n, edges2)
    return after > before


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
    """L_sig: off-diag = +1 for wrap, -1 for non-wrap."""
    L = np.zeros((n, n))
    for u, v in edges:
        L[u, u] += 1
        L[v, v] += 1
        s = +1.0 if (u, v) in W else -1.0
        L[u, v] += s
        L[v, u] += s
    return L


def laplacian_mobius(n, edges, W):
    """L_mob on 2n-dim: diag = deg * I2; off-diag block at (u,v) = -X for wrap,
    -I for non-wrap, where X = [[0,1],[1,0]]."""
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
# Graph operations
# ---------------------------------------------------------------------------

def contract_edge(n, edges, W, e):
    """Contract edge e=(u,v). Merge v into u. Returns (n', edges', W')."""
    u, v = e
    if u > v:
        u, v = v, u
    # Relabel: v -> u; for w > v, w -> w - 1
    def relabel(x):
        if x == v:
            return u
        if x > v:
            return x - 1
        return x

    new_edges = set()
    new_W = set()
    for a, b in edges:
        if (a, b) == e:
            continue
        ra, rb = relabel(a), relabel(b)
        if ra == rb:
            # Self-loop: drop
            continue
        if ra > rb:
            ra, rb = rb, ra
        ne = (ra, rb)
        if ne in new_edges:
            # Parallel edge - simple graph: keep one, but wrap can interact.
            # We'll keep the first encountered wrap status.
            # For robustness, let's XOR wrap bits to simulate "merging"
            if ne in new_W and (a, b) in W:
                new_W.discard(ne)
            elif ne not in new_W and (a, b) in W:
                new_W.add(ne)
            continue
        new_edges.add(ne)
        if (a, b) in W:
            new_W.add(ne)
    return n - 1, sorted(new_edges), new_W


def remove_vertex(n, edges, W, v):
    """Remove vertex v, relabel."""
    def relabel(x):
        if x > v:
            return x - 1
        return x

    new_edges = []
    new_W = set()
    for a, b in edges:
        if a == v or b == v:
            continue
        ra, rb = relabel(a), relabel(b)
        if ra > rb:
            ra, rb = rb, ra
        new_edges.append((ra, rb))
        if (a, b) in W:
            new_W.add((ra, rb))
    return n - 1, new_edges, new_W


def subdivide_edge(n, edges, W, e, k, new_wraps=None):
    """Subdivide edge e into k+1 edges via k new vertices. new_wraps is a list
    of k+1 bools; if None, inherit e's wrap to first only (others non-wrap).
    """
    u, v = e
    if u > v:
        u, v = v, u
    was_wrap = (u, v) in W
    edges2 = [x for x in edges if x != (u, v)]
    W2 = set(W)
    W2.discard((u, v))
    # Introduce new vertices n, n+1, ..., n+k-1
    path = [u] + list(range(n, n + k)) + [v]
    new_n = n + k
    if new_wraps is None:
        # Parity-matched: match original wrap parity - first edge wraps iff original was wrap
        new_wraps = [was_wrap] + [False] * k
    for i in range(len(path) - 1):
        a, b = path[i], path[i + 1]
        if a > b:
            a, b = b, a
        edges2.append((a, b))
        if new_wraps[i]:
            W2.add((a, b))
    edges2.sort()
    return new_n, edges2, W2


def duplicate_edge(n, edges, W, e):
    """Simple graphs: we can't duplicate literally; model via 2-subdivision
    with both edges carrying the same wrap-parity as e (creates a cycle of
    length 2 parallel path)."""
    u, v = e
    if u > v:
        u, v = v, u
    was_wrap = (u, v) in W
    # Add parallel path of length 2 via new vertex w
    w = n
    new_n = n + 1
    new_edges = list(edges)
    new_W = set(W)
    new_edges.append((u, w))
    new_edges.append((v, w))
    if was_wrap:
        # Parity-matched: one of new edges wraps to match parity
        new_W.add((u, w) if u < w else (w, u))
    return new_n, sorted(new_edges), new_W


def disjoint_union(n1, edges1, W1, n2, edges2, W2):
    """Disjoint union with vertex-shift."""
    n = n1 + n2
    new_edges = list(edges1)
    new_W = set(W1)
    for a, b in edges2:
        na, nb = a + n1, b + n1
        new_edges.append((na, nb))
        if (a, b) in W2:
            new_W.add((na, nb))
    new_edges.sort()
    return n, new_edges, new_W


# ---------------------------------------------------------------------------
# Envelope: enumerate (G, W) configs
# ---------------------------------------------------------------------------

def enumerate_all_GW(n_max=5, connected_only=False):
    """Exhaustive enumeration for n<=n_max: all graphs and all wrap subsets."""
    out = []
    for n in range(1, n_max + 1):
        m_max = n * (n - 1) // 2
        for mask in range(1 << m_max):
            edges = edges_from_mask(n, mask)
            if connected_only and n >= 1:
                if num_components(n, edges) != 1:
                    continue
            m = len(edges)
            for w_mask in range(1 << m):
                W = set(edges[i] for i in range(m) if (w_mask >> i) & 1)
                out.append((n, edges, W))
    return out


def sample_n6_configs(count, connected_only=False, seed_offset=0):
    """Random (G, W) on n=6."""
    rng = random.Random(SEED + seed_offset)
    n = 6
    m_max = n * (n - 1) // 2
    out = []
    attempts = 0
    while len(out) < count and attempts < count * 20:
        attempts += 1
        # Bias edge density
        p = rng.uniform(0.2, 0.7)
        edges = []
        for u in range(n):
            for v in range(u + 1, n):
                if rng.random() < p:
                    edges.append((u, v))
        if connected_only and (len(edges) == 0 or num_components(n, edges) != 1):
            continue
        # Random wrap subset
        W = set()
        for e in edges:
            if rng.random() < 0.5:
                W.add(e)
        out.append((n, edges, W))
    return out


# ---------------------------------------------------------------------------
# Claim evaluators
# ---------------------------------------------------------------------------

def claim_C1_trace_power_k(n, edges, W, k):
    """tr(L_mob^k) = tr(L_s^k) + tr(L_sig^k)."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    # Use eigenvalues for speed and numerical sanity
    e_s = eigs(L_s)
    e_sig = eigs(L_sig)
    e_m = eigs(L_m)
    t_s = float(np.sum(e_s ** k))
    t_sig = float(np.sum(e_sig ** k))
    t_m = float(np.sum(e_m ** k))
    diff = abs(t_m - t_s - t_sig)
    rel = diff / max(1.0, abs(t_m))
    return rel < 1e-8, rel


def claim_C2_heat_trace(n, edges, W, t):
    """tr(exp(-t L_mob)) = tr(exp(-t L_s)) + tr(exp(-t L_sig))."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    e_s = eigs(L_s)
    e_sig = eigs(L_sig)
    e_m = eigs(L_m)
    h_s = float(np.sum(np.exp(-t * e_s)))
    h_sig = float(np.sum(np.exp(-t * e_sig)))
    h_m = float(np.sum(np.exp(-t * e_m)))
    diff = abs(h_m - h_s - h_sig)
    rel = diff / max(1.0, abs(h_m))
    return rel < 1e-8, rel


def claim_C3_shifted_det(n, edges, W, alpha):
    """det(L_mob + alpha I) = det(L_s + alpha I) * det(L_sig + alpha I)."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    d_s = float(np.linalg.det(L_s + alpha * np.eye(n)))
    d_sig = float(np.linalg.det(L_sig + alpha * np.eye(n)))
    d_m = float(np.linalg.det(L_m + alpha * np.eye(2 * n)))
    diff = abs(d_m - d_s * d_sig)
    rel = diff / max(1.0, abs(d_m))
    return rel < 1e-6, rel


def claim_C4_resolvent_trace(n, edges, W, alpha):
    """tr((L_mob + alpha I)^-1) = tr((L_s + alpha I)^-1) + tr((L_sig + alpha I)^-1)."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    e_s = eigs(L_s)
    e_sig = eigs(L_sig)
    e_m = eigs(L_m)
    r_s = float(np.sum(1.0 / (e_s + alpha)))
    r_sig = float(np.sum(1.0 / (e_sig + alpha)))
    r_m = float(np.sum(1.0 / (e_m + alpha)))
    diff = abs(r_m - r_s - r_sig)
    rel = diff / max(1.0, abs(r_m))
    return rel < 1e-6, rel


def claim_C5_contraction_lipschitz(n, edges, W, e):
    """|beta(G) - beta(G/e)| <= 1 for non-bridge e."""
    if is_bridge(n, edges, e):
        return None  # skip
    b_before = beta(n, edges, W)
    n2, edges2, W2 = contract_edge(n, edges, W, e)
    b_after = beta(n2, edges2, W2)
    return abs(b_before - b_after) <= 1, abs(b_before - b_after)


def claim_C6_vertex_deletion_lipschitz(n, edges, W, v):
    """|beta(G) - beta(G - v)| <= deg(v)."""
    deg_v = sum(1 for a, b in edges if a == v or b == v)
    b_before = beta(n, edges, W)
    n2, edges2, W2 = remove_vertex(n, edges, W, v)
    b_after = beta(n2, edges2, W2)
    return abs(b_before - b_after) <= max(1, deg_v), abs(b_before - b_after) - deg_v


def claim_C7_vertex_deletion_tight(n, edges, W, v):
    """Tighter: |beta(G) - beta(G - v)| <= 1 + deg(v)? Or just deg(v)?"""
    deg_v = sum(1 for a, b in edges if a == v or b == v)
    b_before = beta(n, edges, W)
    n2, edges2, W2 = remove_vertex(n, edges, W, v)
    b_after = beta(n2, edges2, W2)
    # Claim: bounded by 1 + deg(v)
    return abs(b_before - b_after) <= 1 + deg_v, abs(b_before - b_after)


def claim_C8_disjoint_union_beta(n1, edges1, W1, n2, edges2, W2):
    """beta(G1 disjoint-union G2) = beta(G1) + beta(G2)."""
    b1 = beta(n1, edges1, W1)
    b2 = beta(n2, edges2, W2)
    n, edges, W = disjoint_union(n1, edges1, W1, n2, edges2, W2)
    b = beta(n, edges, W)
    return b == b1 + b2, abs(b - b1 - b2)


def claim_C9_duplicate_edge_beta(n, edges, W, e):
    """Parity-matched 2-parallel-path preserves beta (analogue of 2-subdivision A8)."""
    b_before = beta(n, edges, W)
    n2, edges2, W2 = duplicate_edge(n, edges, W, e)
    b_after = beta(n2, edges2, W2)
    return b_before == b_after, abs(b_before - b_after)


def claim_C10_tr_Ls_Lsig(n, edges, W):
    """Bilinear trace: tr(L_s * L_sig) = tr(L_s^2) - 4|W|."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    lhs = float(np.trace(L_s @ L_sig))
    rhs = float(np.trace(L_s @ L_s) - 4 * len(W))
    diff = abs(lhs - rhs)
    rel = diff / max(1.0, abs(lhs))
    return rel < 1e-8, rel


def claim_C11_tr_Ls_Lmob(n, edges, W):
    """tr((I2 kron L_s) * L_mob) via M6-lifted fact -- check
    tr(L_mob * Proj_even) = tr(L_s) where Proj_even = (1/2)(I + X) kron I_n."""
    # Instead, cleaner: tr(L_mob^2) = tr(L_s^2) + tr(L_sig^2) (k=2 corollary of C1)
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    t_m2 = float(np.trace(L_m @ L_m))
    rhs = float(np.trace(L_s @ L_s) + np.trace(L_sig @ L_sig))
    diff = abs(t_m2 - rhs)
    rel = diff / max(1.0, abs(t_m2))
    return rel < 1e-8, rel


def claim_C12_frobenius_sum(n, edges, W):
    """||L_mob||_F^2 = ||L_s||_F^2 + ||L_sig||_F^2.
    NOTE: this is B17 = M6 corollary. Sanity-only, but make concrete."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    f_m = float(np.sum(L_m * L_m))
    rhs = float(np.sum(L_s * L_s) + np.sum(L_sig * L_sig))
    diff = abs(f_m - rhs)
    rel = diff / max(1.0, abs(f_m))
    return rel < 1e-8, rel


def claim_C13_bridge_wrap_flip_deterministic(n, edges, W, e):
    """For a bridge e, flipping e's wrap changes beta by EXACTLY 0.
    Because: bridges separate components, and toggling wrap on a bridge
    is equivalent to a switching at one of the endpoints of the bridge
    relative to its component, which preserves balance."""
    if not is_bridge(n, edges, e):
        return None
    b_before = beta(n, edges, W)
    # Flip
    if e in W:
        W2 = W - {e}
    else:
        W2 = W | {e}
    b_after = beta(n, edges, W2)
    return b_before == b_after, abs(b_before - b_after)


def claim_C14_nonbridge_wrap_flip_bounded(n, edges, W, e):
    """For a non-bridge e, flipping e's wrap changes beta by at most 1."""
    if is_bridge(n, edges, e):
        return None
    b_before = beta(n, edges, W)
    if e in W:
        W2 = W - {e}
    else:
        W2 = W | {e}
    b_after = beta(n, edges, W2)
    return abs(b_before - b_after) <= 1, abs(b_before - b_after)


def claim_C15_mismatched_subdivision_bounded(n, edges, W, e, k):
    """k-subdivision with ALL new edges wrap-matched to WRONG parity.
    Claim: |beta(G) - beta(G')| <= 1."""
    if k < 1:
        return None
    u, v = e
    if u > v:
        u, v = v, u
    was_wrap = (u, v) in W
    # Wrong parity: flip one bit. Original parity = was_wrap (1 edge of wrap iff was_wrap).
    # Make new path with OPPOSITE total parity.
    new_wraps = [not was_wrap] + [False] * k
    b_before = beta(n, edges, W)
    try:
        n2, edges2, W2 = subdivide_edge(n, edges, W, e, k, new_wraps=new_wraps)
    except Exception:
        return None
    b_after = beta(n2, edges2, W2)
    return abs(b_before - b_after) <= 1, abs(b_before - b_after)


def claim_C16_triangle_closing(n, edges, W, u, v, w, close_wrap):
    """Start with path u-v-w (2 edges). Add closing edge (u,w) with given wrap.
    Claim: if close_wrap parity matches path wrap parity XOR, beta unchanged;
    else beta drops by exactly 1 (within connected component)."""
    # Build path G0: edges (u,v), (v,w) with some wrap; arbitrary rest.
    # Check: if (u,v) and (v,w) exist, and (u,w) not exist, add (u,w) with close_wrap.
    eu_v = (min(u, v), max(u, v))
    ev_w = (min(v, w), max(v, w))
    eu_w = (min(u, w), max(u, w))
    if eu_v not in edges or ev_w not in edges or eu_w in edges:
        return None
    b_before = beta(n, edges, W)
    edges2 = sorted(edges + [eu_w])
    W2 = set(W)
    if close_wrap:
        W2.add(eu_w)
    b_after = beta(n, edges2, W2)
    # Claim: beta decreases by 0 or 1 only (never increases since adding edge inside
    # a comp can only merge or reveal unbalance).
    delta = b_after - b_before
    return delta in (-1, 0), delta


def claim_C17_line_graph_beta_relation(n, edges, W):
    """Line graph L(G) with wrap inherited: edge (e1, e2) in L(G) wraps iff
    e1 and e2 share a vertex and one (but not both) of them is in W.
    Claim: beta(L(G), W_ind) >= 0 (trivial) and related? Test beta(L(G)) <=
    |E(G)|."""
    if len(edges) < 2:
        return None
    # Build line graph
    m = len(edges)
    edge_idx = {e: i for i, e in enumerate(edges)}
    L_edges = []
    L_W = set()
    for i in range(m):
        for j in range(i + 1, m):
            e1, e2 = edges[i], edges[j]
            if set(e1) & set(e2):  # share vertex
                L_edges.append((i, j))
                # Inherited wrap: XOR of the two
                if (e1 in W) ^ (e2 in W):
                    L_W.add((i, j))
    if not L_edges:
        return None
    b_L = beta(m, L_edges, L_W)
    # Trivial bound: beta(L) <= m
    return b_L <= m, b_L


def claim_C18_shifted_det_small(n, edges, W, alpha_list):
    """Multi-alpha check of det identity (more robust)."""
    L_s = laplacian_scalar(n, edges)
    L_sig = laplacian_signed(n, edges, W)
    L_m = laplacian_mobius(n, edges, W)
    max_rel = 0.0
    for alpha in alpha_list:
        d_s = float(np.linalg.det(L_s + alpha * np.eye(n)))
        d_sig = float(np.linalg.det(L_sig + alpha * np.eye(n)))
        d_m = float(np.linalg.det(L_m + alpha * np.eye(2 * n)))
        diff = abs(d_m - d_s * d_sig)
        rel = diff / max(1.0, abs(d_m))
        if rel > max_rel:
            max_rel = rel
    return max_rel < 1e-6, max_rel


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def mk_result():
    return {"n_pass": 0, "n_total": 0, "min_val": None, "max_val": None,
            "counterexamples": []}


def update_result(r, ok, val, ce=None, max_ce=5):
    r["n_total"] += 1
    if ok:
        r["n_pass"] += 1
    else:
        if len(r["counterexamples"]) < max_ce and ce is not None:
            r["counterexamples"].append(ce)
    if val is not None:
        if r["min_val"] is None or val < r["min_val"]:
            r["min_val"] = val
        if r["max_val"] is None or val > r["max_val"]:
            r["max_val"] = val


def tau(r):
    if r["n_total"] == 0:
        return None
    return r["n_pass"] / r["n_total"]


def main():
    t0 = time.time()
    results = {}

    # --- Build envelopes ---
    print("[envelope] Building small-graph envelopes ...", flush=True)

    # n<=4: full exhaustive for all claims
    full_small = enumerate_all_GW(n_max=4)
    print(f"[envelope]   n<=4 all: {len(full_small)}", flush=True)

    # n=5: full exhaustive, but that's 2^(10) * 2^10 worst case = 1M - cap by edge count
    # Instead, enumerate all graphs on 5 but cap wrap per graph to 8.
    full_5 = []
    for mask in range(1 << 10):
        edges = edges_from_mask(5, mask)
        m = len(edges)
        all_W = list(itertools.chain.from_iterable(
            itertools.combinations(edges, r) for r in range(m + 1)))
        if len(all_W) > 12:
            all_W = RNG.sample(all_W, 12)
        for wsub in all_W:
            full_5.append((5, edges, set(wsub)))
    print(f"[envelope]   n=5 sampled wraps: {len(full_5)}", flush=True)

    # n=6 sample: ~300 per claim
    sample_6 = sample_n6_configs(350)
    sample_6_conn = sample_n6_configs(200, connected_only=True, seed_offset=1)
    print(f"[envelope]   n=6 sample: {len(sample_6)} / conn {len(sample_6_conn)}",
          flush=True)

    envelope_main = full_small + full_5 + sample_6
    envelope_conn = [(n, e, w) for (n, e, w) in envelope_main
                     if n > 0 and num_components(n, e) == 1]
    # Cap the connected-only envelope to speed up per-edge loops
    if len(envelope_conn) > 1500:
        envelope_conn = RNG.sample(envelope_conn, 1500)
    print(f"[envelope]   main {len(envelope_main)} / connected {len(envelope_conn)}",
          flush=True)

    # --- Claims C1: trace-power k=1..10 ---
    print("\n[C1] trace-power identity tr(L_mob^k) = tr(L_s^k) + tr(L_sig^k) k=1..10", flush=True)
    for k in range(1, 11):
        key = f"C1_k{k}"
        results[key] = mk_result()
        results[key]["claim"] = f"tr(L_mob^{k}) = tr(L_s^{k}) + tr(L_sig^{k})"
        results[key]["direction"] = 1
        for n, edges, W in envelope_main:
            if n == 0:
                continue
            ok, rel = claim_C1_trace_power_k(n, edges, W, k)
            update_result(results[key], ok, rel,
                          ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
        r = results[key]
        print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
              f"max_rel={r['max_val']}", flush=True)

    # --- C2: heat trace at several t ---
    print("\n[C2] heat trace tr(exp(-t L_mob)) = tr(exp(-t L_s)) + tr(exp(-t L_sig))",
          flush=True)
    for t_val in [0.1, 0.5, 1.0, 2.0]:
        key = f"C2_t{t_val}"
        results[key] = mk_result()
        results[key]["claim"] = f"tr(exp(-{t_val}*L_mob)) = tr(exp(-{t_val}*L_s)) + tr(exp(-{t_val}*L_sig))"
        results[key]["direction"] = 1
        for n, edges, W in envelope_main:
            if n == 0:
                continue
            ok, rel = claim_C2_heat_trace(n, edges, W, t_val)
            update_result(results[key], ok, rel,
                          ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
        r = results[key]
        print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
              f"max_rel={r['max_val']}", flush=True)

    # --- C3: shifted-det (multi alpha) ---
    print("\n[C3] det(L_mob + aI) = det(L_s + aI) * det(L_sig + aI)", flush=True)
    for alpha in [0.5, 1.0, 2.0]:
        key = f"C3_a{alpha}"
        results[key] = mk_result()
        results[key]["claim"] = f"det(L_mob + {alpha}I) = det(L_s + {alpha}I) * det(L_sig + {alpha}I)"
        results[key]["direction"] = 1
        for n, edges, W in envelope_main:
            if n == 0:
                continue
            ok, rel = claim_C3_shifted_det(n, edges, W, alpha)
            update_result(results[key], ok, rel,
                          ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
        r = results[key]
        print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
              f"max_rel={r['max_val']}", flush=True)

    # --- C4: resolvent trace ---
    print("\n[C4] resolvent trace tr((L_mob + aI)^-1) = tr((L_s+aI)^-1) + tr((L_sig+aI)^-1)",
          flush=True)
    for alpha in [0.5, 1.0, 2.0]:
        key = f"C4_a{alpha}"
        results[key] = mk_result()
        results[key]["claim"] = f"tr((L_mob+{alpha}I)^-1) = tr((L_s+{alpha}I)^-1) + tr((L_sig+{alpha}I)^-1)"
        results[key]["direction"] = 1
        for n, edges, W in envelope_main:
            if n == 0:
                continue
            ok, rel = claim_C4_resolvent_trace(n, edges, W, alpha)
            update_result(results[key], ok, rel,
                          ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
        r = results[key]
        print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
              f"max_rel={r['max_val']}", flush=True)

    # --- C5: contraction-Lipschitz ---
    print("\n[C5] |beta(G) - beta(G/e)| <= 1 for non-bridge e", flush=True)
    key = "C5"
    results[key] = mk_result()
    results[key]["claim"] = "|beta(G) - beta(G/e)| <= 1 for non-bridge e"
    results[key]["direction"] = 2
    n_edges_seen = 0
    for n, edges, W in envelope_main:
        if n < 2:
            continue
        for e in edges:
            n_edges_seen += 1
            if n_edges_seen > 5000:
                break
            res = claim_C5_contraction_lipschitz(n, edges, W, e)
            if res is None:
                continue
            ok, delta = res
            update_result(results[key], ok, delta,
                          ce={"n": n, "edges": edges, "W": list(W), "e": e,
                              "delta": delta})
        if n_edges_seen > 5000:
            break
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_delta={r['max_val']}", flush=True)

    # --- C6: vertex-deletion Lipschitz |dB| <= deg(v) ---
    print("\n[C6] |beta(G) - beta(G-v)| <= deg(v)", flush=True)
    key = "C6"
    results[key] = mk_result()
    results[key]["claim"] = "|beta(G) - beta(G-v)| <= deg(v)"
    results[key]["direction"] = 2
    n_v_seen = 0
    for n, edges, W in envelope_main:
        if n < 2:
            continue
        for v in range(n):
            n_v_seen += 1
            if n_v_seen > 5000:
                break
            deg_v = sum(1 for a, b in edges if a == v or b == v)
            b_before = beta(n, edges, W)
            n2, edges2, W2 = remove_vertex(n, edges, W, v)
            b_after = beta(n2, edges2, W2)
            diff = abs(b_before - b_after)
            ok = diff <= deg_v
            update_result(results[key], ok, diff - deg_v,
                          ce={"n": n, "edges": edges, "W": list(W),
                              "v": v, "deg_v": deg_v, "diff": diff})
        if n_v_seen > 5000:
            break
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max(diff-deg)={r['max_val']}", flush=True)

    # --- C7: vertex-deletion Lipschitz |dB| <= 1 + deg(v) ---
    print("\n[C7] |beta(G) - beta(G-v)| <= 1 + deg(v)", flush=True)
    key = "C7"
    results[key] = mk_result()
    results[key]["claim"] = "|beta(G) - beta(G-v)| <= 1 + deg(v)"
    results[key]["direction"] = 2
    n_v_seen = 0
    for n, edges, W in envelope_main:
        if n < 2:
            continue
        for v in range(n):
            n_v_seen += 1
            if n_v_seen > 5000:
                break
            deg_v = sum(1 for a, b in edges if a == v or b == v)
            b_before = beta(n, edges, W)
            n2, edges2, W2 = remove_vertex(n, edges, W, v)
            b_after = beta(n2, edges2, W2)
            diff = abs(b_before - b_after)
            ok = diff <= 1 + deg_v
            update_result(results[key], ok, diff - (1 + deg_v),
                          ce={"n": n, "edges": edges, "W": list(W),
                              "v": v, "deg_v": deg_v, "diff": diff})
        if n_v_seen > 5000:
            break
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max(diff-1-deg)={r['max_val']}", flush=True)

    # --- C8: disjoint union beta additivity ---
    print("\n[C8] beta(G1 disjoint-union G2) = beta(G1) + beta(G2)", flush=True)
    key = "C8"
    results[key] = mk_result()
    results[key]["claim"] = "beta(G1 du G2) = beta(G1) + beta(G2)"
    results[key]["direction"] = 4
    # Cross product of small-graph configs (limit to keep tractable)
    small_configs = [c for c in full_small if c[0] <= 3]
    for i, (n1, e1, W1) in enumerate(small_configs):
        if i > 200:
            break
        for j, (n2, e2, W2) in enumerate(small_configs):
            if j > 200:
                break
            ok, diff = claim_C8_disjoint_union_beta(n1, e1, W1, n2, e2, W2)
            update_result(results[key], ok, diff,
                          ce={"n1": n1, "e1": e1, "W1": list(W1),
                              "n2": n2, "e2": e2, "W2": list(W2), "diff": diff})
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_diff={r['max_val']}", flush=True)

    # --- C9: duplicate-edge preserves beta (parallel-path) ---
    print("\n[C9] Parallel-path doubling of edge preserves beta (parity-matched)", flush=True)
    key = "C9"
    results[key] = mk_result()
    results[key]["claim"] = "2-parallel-path with parity-matched wraps preserves beta"
    results[key]["direction"] = 4
    edges_seen = 0
    for n, edges, W in envelope_main:
        if n < 2 or not edges:
            continue
        for e in edges:
            edges_seen += 1
            if edges_seen > 3000:
                break
            ok, delta = claim_C9_duplicate_edge_beta(n, edges, W, e)
            update_result(results[key], ok, delta,
                          ce={"n": n, "edges": edges, "W": list(W), "e": e,
                              "delta": delta})
        if edges_seen > 3000:
            break
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_delta={r['max_val']}", flush=True)

    # --- C10: tr(L_s * L_sig) = tr(L_s^2) - 4|W| ---
    print("\n[C10] tr(L_s * L_sig) = tr(L_s^2) - 4|W|", flush=True)
    key = "C10"
    results[key] = mk_result()
    results[key]["claim"] = "tr(L_s * L_sig) = tr(L_s^2) - 4|W|"
    results[key]["direction"] = 3
    for n, edges, W in envelope_main:
        if n == 0:
            continue
        ok, rel = claim_C10_tr_Ls_Lsig(n, edges, W)
        update_result(results[key], ok, rel,
                      ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_rel={r['max_val']}", flush=True)

    # --- C11: tr(L_mob^2) = tr(L_s^2) + tr(L_sig^2) ---
    print("\n[C11] tr(L_mob^2) = tr(L_s^2) + tr(L_sig^2) (concrete k=2 of M6)", flush=True)
    key = "C11"
    results[key] = mk_result()
    results[key]["claim"] = "tr(L_mob^2) = tr(L_s^2) + tr(L_sig^2)"
    results[key]["direction"] = 3
    for n, edges, W in envelope_main:
        if n == 0:
            continue
        ok, rel = claim_C11_tr_Ls_Lmob(n, edges, W)
        update_result(results[key], ok, rel,
                      ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_rel={r['max_val']}", flush=True)

    # --- C12: Frobenius ---
    print("\n[C12] ||L_mob||_F^2 = ||L_s||_F^2 + ||L_sig||_F^2 (B17 concrete)", flush=True)
    key = "C12"
    results[key] = mk_result()
    results[key]["claim"] = "||L_mob||_F^2 = ||L_s||_F^2 + ||L_sig||_F^2"
    results[key]["direction"] = 3
    for n, edges, W in envelope_main:
        if n == 0:
            continue
        ok, rel = claim_C12_frobenius_sum(n, edges, W)
        update_result(results[key], ok, rel,
                      ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_rel={r['max_val']}", flush=True)

    # --- C13: bridge wrap-flip deterministic (beta unchanged) ---
    print("\n[C13] Flipping wrap on a BRIDGE preserves beta", flush=True)
    key = "C13"
    results[key] = mk_result()
    results[key]["claim"] = "Flipping wrap on a bridge preserves beta"
    results[key]["direction"] = 5
    edges_seen = 0
    for n, edges, W in envelope_main:
        if n < 2 or not edges:
            continue
        for e in edges:
            edges_seen += 1
            if edges_seen > 5000:
                break
            res = claim_C13_bridge_wrap_flip_deterministic(n, edges, W, e)
            if res is None:
                continue
            ok, delta = res
            update_result(results[key], ok, delta,
                          ce={"n": n, "edges": edges, "W": list(W), "e": e,
                              "delta": delta})
        if edges_seen > 5000:
            break
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_delta={r['max_val']}", flush=True)

    # --- C14: non-bridge wrap-flip bounded |dB| <= 1 ---
    print("\n[C14] Flipping wrap on a NON-bridge: |dbeta| <= 1", flush=True)
    key = "C14"
    results[key] = mk_result()
    results[key]["claim"] = "Flipping wrap on a non-bridge: |dbeta| <= 1"
    results[key]["direction"] = 5
    edges_seen = 0
    for n, edges, W in envelope_main:
        if n < 2 or not edges:
            continue
        for e in edges:
            edges_seen += 1
            if edges_seen > 5000:
                break
            res = claim_C14_nonbridge_wrap_flip_bounded(n, edges, W, e)
            if res is None:
                continue
            ok, delta = res
            update_result(results[key], ok, delta,
                          ce={"n": n, "edges": edges, "W": list(W), "e": e,
                              "delta": delta})
        if edges_seen > 5000:
            break
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_delta={r['max_val']}", flush=True)

    # --- C15: mismatched-parity subdivision |dB| <= 1 ---
    print("\n[C15] Mismatched-parity k-subdivision: |dbeta| <= 1 (k=2,3)", flush=True)
    for k in [2, 3]:
        key = f"C15_k{k}"
        results[key] = mk_result()
        results[key]["claim"] = f"k={k} subdivision with mismatched parity: |dbeta| <= 1"
        results[key]["direction"] = 5
        edges_seen = 0
        for n, edges, W in envelope_main:
            if n < 2 or not edges or n >= 6:
                continue  # skip n=6 since n+k may blow out
            for e in edges:
                edges_seen += 1
                if edges_seen > 3000:
                    break
                res = claim_C15_mismatched_subdivision_bounded(n, edges, W, e, k)
                if res is None:
                    continue
                ok, delta = res
                update_result(results[key], ok, delta,
                              ce={"n": n, "edges": edges, "W": list(W), "e": e,
                                  "k": k, "delta": delta})
            if edges_seen > 3000:
                break
        r = results[key]
        print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
              f"max_delta={r['max_val']}", flush=True)

    # --- C16: triangle-closing beta change in {-1, 0} ---
    print("\n[C16] Triangle-closing (path u-v-w + edge (u,w)): dbeta in {-1, 0}",
          flush=True)
    for close_wrap in [False, True]:
        key = f"C16_w{int(close_wrap)}"
        results[key] = mk_result()
        results[key]["claim"] = f"Triangle closing with wrap={close_wrap}: dbeta in {{-1,0}}"
        results[key]["direction"] = 5
        triples_seen = 0
        for n, edges, W in envelope_main:
            if n < 3 or len(edges) < 2:
                continue
            for u in range(n):
                for v in range(n):
                    for w in range(n):
                        if len({u, v, w}) != 3:
                            continue
                        triples_seen += 1
                        if triples_seen > 2000:
                            break
                        res = claim_C16_triangle_closing(n, edges, W, u, v, w, close_wrap)
                        if res is None:
                            continue
                        ok, delta = res
                        update_result(results[key], ok, delta,
                                      ce={"n": n, "edges": edges, "W": list(W),
                                          "u": u, "v": v, "w": w,
                                          "close_wrap": close_wrap, "delta": delta})
                    if triples_seen > 2000:
                        break
                if triples_seen > 2000:
                    break
            if triples_seen > 2000:
                break
        r = results[key]
        print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
              f"delta range=[{r['min_val']}, {r['max_val']}]", flush=True)

    # --- C17: line-graph beta bound ---
    print("\n[C17] beta(L(G), W_induced) <= |E(G)| (trivial sanity)", flush=True)
    key = "C17"
    results[key] = mk_result()
    results[key]["claim"] = "beta(L(G), W_induced_XOR) <= |E(G)|"
    results[key]["direction"] = 4
    n_seen = 0
    for n, edges, W in envelope_main:
        if n < 3 or len(edges) < 2:
            continue
        n_seen += 1
        if n_seen > 1000:
            break
        res = claim_C17_line_graph_beta_relation(n, edges, W)
        if res is None:
            continue
        ok, b_L = res
        update_result(results[key], ok, b_L,
                      ce={"n": n, "edges": edges, "W": list(W), "b_L": b_L})
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"b_L range=[{r['min_val']}, {r['max_val']}]", flush=True)

    # --- C18: Kemeny/Ratcliff-like multi-alpha identity stability ---
    print("\n[C18] Multi-alpha det identity robustness check", flush=True)
    key = "C18"
    results[key] = mk_result()
    results[key]["claim"] = "det identity stable across alpha = {0.25, 0.5, 1, 2, 4}"
    results[key]["direction"] = 1
    alphas = [0.25, 0.5, 1.0, 2.0, 4.0]
    for n, edges, W in envelope_main[:2000]:
        if n == 0:
            continue
        ok, rel = claim_C18_shifted_det_small(n, edges, W, alphas)
        update_result(results[key], ok, rel,
                      ce={"n": n, "edges": edges, "W": list(W), "rel": rel})
    r = results[key]
    print(f"  {key}: tau={tau(r):.6f} pass {r['n_pass']}/{r['n_total']} "
          f"max_rel={r['max_val']}", flush=True)

    # --- Final summary ---
    t1 = time.time()
    print(f"\n[summary] elapsed {t1 - t0:.1f}s", flush=True)
    print("=" * 72, flush=True)
    print(f"{'id':<10} {'dir':<4} {'tau':<10} {'pass/total':<14} verdict", flush=True)
    print("-" * 72, flush=True)
    summary = []
    for key, r in results.items():
        t = tau(r)
        if t is None:
            verdict = "skipped"
        elif t >= 0.999:
            verdict = "PROMOTE"
        elif t >= 0.95:
            verdict = "refine"
        elif t >= 0.5:
            verdict = "weak"
        else:
            verdict = "dead"
        print(f"{key:<10} {r.get('direction', '?'):<4} "
              f"{t if t is not None else 0.0:<10.6f} "
              f"{r['n_pass']}/{r['n_total']:<10} {verdict}", flush=True)
        summary.append({"id": key, "direction": r.get("direction"),
                        "claim": r.get("claim"), "tau": t,
                        "pass": r["n_pass"], "total": r["n_total"],
                        "verdict": verdict, "min_val": r["min_val"],
                        "max_val": r["max_val"],
                        "counterexamples": r["counterexamples"][:3]})

    # Write results.json
    out_dir = Path(__file__).parent
    with open(out_dir / "results.json", "w", encoding="utf-8") as f:
        json.dump({"seed": SEED, "elapsed_s": t1 - t0, "results": summary}, f,
                  indent=2, default=str)
    print(f"\n[write] results.json written ({len(summary)} claims)", flush=True)


if __name__ == "__main__":
    main()
