"""
FUZZER-A R6 Stage 2 — sheaf-section α (edge-ops at scale).

Scale-tests the τ=1 α-claims from Stage 1 at n=6 with broad wrap-coverage,
fuzzes the Tier-6 one-sided inequalities A5' and A6', and spot-checks L15
(monotonicity of β under non-bridge non-wrap deletion).

Budget ~15 minutes wall-clock. Pure Python + networkx.

Target claims:

  Preservation claims (scale tests, n=6):
    A2   Adding a pendant non-wrap edge preserves β.
    A3   Adding a pendant wrap edge preserves β.
    A8   k-subdivision of edge e with Σ(new wrap bits) ≡ [e ∈ W] (mod 2)
         preserves β, for k ∈ {2, 3}.
    A10  Adding two new edges commutes (order-independent for β).
    A12  Theta-replacement of a non-wrap edge by two parallel length-2
         non-wrap paths preserves β.
    A13  Vertex-switching invariance: β(G, W) = β(G, W △ δ({v})).

  One-sided inequality candidates (Tier-6):
    A5'  β(G, W) ≤ β(G/e, W') for non-bridge non-wrap e (contraction mono).
    A6'  β(G, W) ≤ β(G/switched(e), W') for wrap non-bridge e
         (switch-then-contract monotonicity).

  Cross-check:
    L15  β(G, W) ≤ β(G.eraseEdge e, W) for non-bridge non-wrap e (already
         landed; re-verify at n=6 sample ≥ 1000).  Also test reverse
         Lipschitz bound β(G.eraseEdge e, W) ≤ β(G, W) + 1.

Writes results.json and human-readable tables to stdout.
"""

from __future__ import annotations

import itertools
import json
import random
import sys
import time
from pathlib import Path

import networkx as nx


RNG = random.Random(20260422)
N6_TARGET_CONNECTED_GRAPHS = 350    # lower bound of labeled connected graphs per run
N6_WRAP_SAMPLES_PER_GRAPH = 16      # minimum wrap subsets per graph
N6_INEQ_SAMPLE = 2200               # sample configs for n=6 inequality fuzz
L15_SAMPLE_N6 = 1500                # cross-check L15 at n=6

# ---------------------------------------------------------------------------
# β helpers.
# ---------------------------------------------------------------------------

def edge_list(G):
    return [tuple(sorted(e)) for e in G.edges()]


def is_balanced_component(H, wrap_H):
    """BFS two-colour on component H with edge-flips given by wrap_H.
    Returns True iff balanced (no odd-signed cycle)."""
    color = {}
    for root in H.nodes():
        if root in color:
            continue
        color[root] = 0
        stack = [root]
        while stack:
            u = stack.pop()
            for w in H.neighbors(u):
                e = tuple(sorted((u, w)))
                flip = 1 if e in wrap_H else 0
                expected = color[u] ^ flip
                if w not in color:
                    color[w] = expected
                    stack.append(w)
                elif color[w] != expected:
                    return False
    return True


def beta(G, wrap):
    """β(G, W) = number of balanced connected components."""
    cnt = 0
    for comp in nx.connected_components(G):
        H = G.subgraph(comp)
        H_edges = set(tuple(sorted(e)) for e in H.edges())
        wrap_H = wrap & H_edges
        if is_balanced_component(H, wrap_H):
            cnt += 1
    return cnt


def bridges(G):
    return set(tuple(sorted(e)) for e in nx.bridges(G))


# ---------------------------------------------------------------------------
# Labeled-connected enumeration / sampling at n=6.
# ---------------------------------------------------------------------------

def all_labeled_graphs(n):
    nodes = list(range(n))
    potential = list(itertools.combinations(nodes, 2))
    m = len(potential)
    for mask in range(1 << m):
        edges = [potential[i] for i in range(m) if mask & (1 << i)]
        G = nx.Graph()
        G.add_nodes_from(nodes)
        G.add_edges_from(edges)
        yield G


def random_connected_graph(n, p_low=0.25, p_high=0.75, max_tries=1000):
    """Sample a labeled connected graph on {0,...,n-1}; reject disconnected."""
    for _ in range(max_tries):
        p = RNG.uniform(p_low, p_high)
        G = nx.gnp_random_graph(n, p, seed=RNG.randint(0, 2**31 - 1))
        if nx.is_connected(G):
            return G
    # fallback: cycle
    G = nx.cycle_graph(n)
    return G


def sample_connected_n6_graphs(target_count):
    """Returns `target_count` labeled connected graphs on 6 nodes, with
    varying density. Mixes canonical-density samples with random-density."""
    graphs = []
    # Include a small exhaustive slice for tiny |E|.
    seen_canon = set()
    for G in all_labeled_graphs(6):
        if G.number_of_edges() <= 7 and nx.is_connected(G):
            # Weisfeiler-Lehman canon
            canon = nx.weisfeiler_lehman_graph_hash(G)
            # sample a handful per canon
            k = seen_canon.count(canon) if hasattr(seen_canon, "count") else 0
            if canon not in seen_canon:
                seen_canon.add(canon)
                graphs.append(G)
                if len(graphs) >= target_count // 3:
                    break
    # Random top-up
    while len(graphs) < target_count:
        graphs.append(random_connected_graph(6))
    return graphs


def random_wrap_subsets(G, count):
    """Yield up to `count` random wrap subsets of G.edges(), covering varying
    |W| ∈ {0, ..., |E|}."""
    edges = edge_list(G)
    m = len(edges)
    if m == 0:
        yield frozenset()
        return
    out = set()
    # cover each |W| level at least once when feasible.
    levels = list(range(m + 1))
    RNG.shuffle(levels)
    for r in levels:
        sub = frozenset(RNG.sample(edges, r)) if r > 0 else frozenset()
        if sub not in out:
            out.add(sub)
            yield sub
        if len(out) >= count:
            return
    # then uniform random masks
    attempts = 0
    while len(out) < count and attempts < count * 4:
        mask = RNG.randrange(1 << m)
        sub = frozenset(edges[i] for i in range(m) if mask & (1 << i))
        if sub not in out:
            out.add(sub)
            yield sub
        attempts += 1


# ---------------------------------------------------------------------------
# FuzzyClaim container.
# ---------------------------------------------------------------------------

class FuzzyClaim:
    def __init__(self, key, name):
        self.key = key
        self.name = name
        self.tested = 0
        self.passed = 0
        self.ces = []

    def record(self, ok, ce=None):
        self.tested += 1
        if ok:
            self.passed += 1
        elif ce is not None and len(self.ces) < 8:
            self.ces.append(ce)

    @property
    def tau(self):
        return 0.0 if self.tested == 0 else self.passed / self.tested

    def verdict(self):
        t = self.tau
        if self.tested == 0:
            return "NO DATA"
        if t == 1.0:
            return f"PASS (τ=1.0000, n={self.tested})"
        if t > 0.99:
            return f"NEAR-PASS (τ={t:.4f})"
        if t > 0.5:
            return f"MOSTLY (τ={t:.4f})"
        return f"COUNTEREX-RICH (τ={t:.4f})"

    def to_dict(self):
        return {
            "key": self.key,
            "name": self.name,
            "tested": self.tested,
            "passed": self.passed,
            "tau": round(self.tau, 6),
            "verdict": self.verdict(),
            "counterexamples": self.ces,
        }


# ---------------------------------------------------------------------------
# Graph-op helpers.
# ---------------------------------------------------------------------------

def relabel(G, W):
    mapping = {old: new for new, old in enumerate(sorted(G.nodes()))}
    Gr = nx.relabel_nodes(G, mapping)
    Wr = frozenset(
        tuple(sorted((mapping[a], mapping[b]))) for (a, b) in W
        if a in mapping and b in mapping
    )
    return Gr, Wr


def vertex_switch(G, W, v):
    new_W = set(W)
    for u in G.neighbors(v):
        e = tuple(sorted((u, v)))
        if e in new_W:
            new_W.discard(e)
        else:
            new_W.add(e)
    return frozenset(new_W)


def contract_edge_signed(G, W, e):
    """Contract edge e in simple graph G; W drops e itself, and edges that
    become parallel to a retained edge are XOR-reduced... but in a simple
    graph model we instead drop duplicates to the FIRST-WINS rule (we
    keep the existing edge's wrap bit; if the new parallel edge has a
    DIFFERENT wrap bit we flag the ambiguity as "contraction-conflict",
    which we treat as the retained bit = XOR of both — the physically
    correct choice under signed-graph contraction).

    Self-loops are dropped (simple graph model).
    """
    u, v = e
    # canonical: merge v into u.
    Gp = nx.Graph()
    Gp.add_nodes_from(n for n in G.nodes() if n != v)
    Wp = set()
    existing = {}      # edge -> wrap bit
    for a, b in G.edges():
        if (a, b) == e or (b, a) == e:
            continue  # contracted edge
        a2 = u if a == v else a
        b2 = u if b == v else b
        if a2 == b2:
            continue  # self-loop, drop
        ee = tuple(sorted((a2, b2)))
        orig = tuple(sorted((a, b)))
        bit = 1 if orig in W else 0
        if ee in existing:
            # XOR-merge parallel edges (standard for signed-graph contraction
            # when identifying parallel edges as a single edge in the simple
            # model).
            existing[ee] = existing[ee] ^ bit
        else:
            existing[ee] = bit
    for ee, bit in existing.items():
        Gp.add_edge(*ee)
        if bit:
            Wp.add(ee)
    return Gp, frozenset(Wp)


# ---------------------------------------------------------------------------
# α preservation claims (scale-test at n=6).
# ---------------------------------------------------------------------------

def test_A2(G, W, c):
    """Pendant non-wrap edge: add fresh vertex w = n, edge (v, w) ∉ W."""
    n = max(G.nodes()) + 1
    for v in G.nodes():
        Gp = G.copy()
        w = n
        Gp.add_node(w)
        Gp.add_edge(v, w)
        b1 = beta(G, W)
        b2 = beta(Gp, W)
        ok = (b1 == b2)
        c.record(ok, None if ok else {
            "claim": "A2", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "v": v,
            "beta_G": b1, "beta_Gp": b2,
        })


def test_A3(G, W, c):
    """Pendant wrap edge."""
    n = max(G.nodes()) + 1
    for v in G.nodes():
        Gp = G.copy()
        w = n
        Gp.add_node(w)
        new_e = tuple(sorted((v, w)))
        Gp.add_edge(*new_e)
        Wp = frozenset(set(W) | {new_e})
        b1 = beta(G, W)
        b2 = beta(Gp, Wp)
        ok = (b1 == b2)
        c.record(ok, None if ok else {
            "claim": "A3", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "v": v,
            "beta_G": b1, "beta_Gp": b2,
        })


def subdivide_edge_with_wrap_mask(G, W, e, mask_bits, base_label):
    """Replace (u,v) by u-w_1-...-w_{k-1}-v.  mask_bits[i] = 1 ⇒ new edge i
    is wrap.  Length of chain = k = len(mask_bits). k-1 fresh vertices."""
    u, v = e
    k = len(mask_bits)
    Gp = G.copy()
    Gp.remove_edge(u, v)
    new_nodes = [base_label + i for i in range(k - 1)]
    for w in new_nodes:
        Gp.add_node(w)
    chain = [u] + new_nodes + [v]
    Wp = set(W)
    if e in Wp:
        Wp.discard(e)
    for i, (a, b) in enumerate(zip(chain, chain[1:])):
        edge = tuple(sorted((a, b)))
        Gp.add_edge(*edge)
        if mask_bits[i]:
            Wp.add(edge)
    return Gp, frozenset(Wp)


def test_A8(G, W, c, k_values=(2, 3), edge_cap=4, mask_cap=8):
    """k-subdivision with Σ bits ≡ [e ∈ W] (mod 2). k ∈ {2, 3}."""
    n = max(G.nodes()) + 1
    edges = edge_list(G)
    if len(edges) > edge_cap:
        edges_sampled = RNG.sample(edges, edge_cap)
    else:
        edges_sampled = edges
    for e in edges_sampled:
        orig_parity = 1 if e in W else 0
        for k in k_values:
            # collect masks with the right parity
            all_masks = [m for m in range(1 << k)
                         if bin(m).count("1") % 2 == orig_parity]
            if len(all_masks) > mask_cap:
                all_masks = RNG.sample(all_masks, mask_cap)
            for mask in all_masks:
                bits = [(mask >> i) & 1 for i in range(k)]
                Gp, Wp = subdivide_edge_with_wrap_mask(G, W, e, bits,
                                                      base_label=n)
                b1 = beta(G, W)
                b2 = beta(Gp, Wp)
                ok = (b1 == b2)
                c.record(ok, None if ok else {
                    "claim": "A8", "n": G.number_of_nodes(),
                    "edges": edge_list(G), "W": sorted(W),
                    "subdivided": list(e), "k": k, "mask": bits,
                    "beta_G": b1, "beta_Gp": b2,
                })


def test_A10(G, W, c, pair_cap=6):
    """Add two new edges — order-independent for β."""
    edges = set(edge_list(G))
    V = list(G.nodes())
    all_pairs = [tuple(sorted((u, v)))
                 for u, v in itertools.combinations(V, 2)]
    non_edges = [p for p in all_pairs if p not in edges]
    if len(non_edges) < 2:
        return
    pairs = list(itertools.combinations(non_edges, 2))
    if len(pairs) > pair_cap:
        pairs = RNG.sample(pairs, pair_cap)
    for e1, e2 in pairs:
        for w_flags in itertools.product((0, 1), repeat=2):
            G1 = G.copy(); G1.add_edge(*e1); G1.add_edge(*e2)
            G2 = G.copy(); G2.add_edge(*e2); G2.add_edge(*e1)
            W_new = set(W)
            if w_flags[0]: W_new.add(e1)
            if w_flags[1]: W_new.add(e2)
            W_new = frozenset(W_new)
            b1 = beta(G1, W_new)
            b2 = beta(G2, W_new)
            ok = (b1 == b2)
            c.record(ok, None if ok else {
                "claim": "A10", "n": G.number_of_nodes(),
                "edges": edge_list(G), "W": sorted(W),
                "e1": list(e1), "e2": list(e2), "w_flags": w_flags,
                "b1": b1, "b2": b2,
            })


def test_A12(G, W, c, edge_cap=4):
    """Theta-replacement: e=(u,v) ∉ W → delete e, add fresh w1, w2, edges
    u-w1, w1-v, u-w2, w2-v (all non-wrap)."""
    n = max(G.nodes()) + 1
    edges = [e for e in edge_list(G) if e not in W]
    if len(edges) > edge_cap:
        edges = RNG.sample(edges, edge_cap)
    for e in edges:
        u, v = e
        Gp = G.copy()
        Gp.remove_edge(u, v)
        w1, w2 = n, n + 1
        Gp.add_node(w1); Gp.add_node(w2)
        Gp.add_edge(u, w1); Gp.add_edge(w1, v)
        Gp.add_edge(u, w2); Gp.add_edge(w2, v)
        Wp = frozenset(set(W) - {e})
        b1 = beta(G, W)
        b2 = beta(Gp, Wp)
        ok = (b1 == b2)
        c.record(ok, None if ok else {
            "claim": "A12", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "e": list(e),
            "beta_G": b1, "beta_Gp": b2,
        })


def test_A13(G, W, c):
    """Vertex-switching invariance."""
    for v in G.nodes():
        Wsw = vertex_switch(G, W, v)
        b1 = beta(G, W)
        b2 = beta(G, Wsw)
        ok = (b1 == b2)
        c.record(ok, None if ok else {
            "claim": "A13", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "v": v,
            "b1": b1, "b2": b2,
        })


# ---------------------------------------------------------------------------
# Tier-6 one-sided inequalities.
# ---------------------------------------------------------------------------

def test_A5prime(G, W, c, edge_cap=None):
    """A5': β(G, W) ≤ β(G/e, W') for non-bridge non-wrap e, G connected."""
    if not nx.is_connected(G):
        return
    br = bridges(G)
    edges = [e for e in edge_list(G) if e not in W and e not in br]
    if edge_cap is not None and len(edges) > edge_cap:
        edges = RNG.sample(edges, edge_cap)
    for e in edges:
        Gp, Wp = contract_edge_signed(G, W, e)
        Gp, Wp = relabel(Gp, Wp)
        b1 = beta(G, W)
        b2 = beta(Gp, Wp)
        ok = (b1 <= b2)
        c.record(ok, None if ok else {
            "claim": "A5'", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "e": list(e),
            "beta_G": b1, "beta_contracted": b2,
        })


def test_A6prime(G, W, c, edge_cap=None):
    """A6': β(G, W) ≤ β(G/switched(e), W') for non-bridge wrap e.
    "switched(e)": switch at one endpoint u (so e becomes non-wrap), then
    contract e."""
    if not nx.is_connected(G):
        return
    br = bridges(G)
    wrap_edges = [e for e in edge_list(G) if e in W and e not in br]
    if edge_cap is not None and len(wrap_edges) > edge_cap:
        wrap_edges = RNG.sample(wrap_edges, edge_cap)
    for e in wrap_edges:
        u, v = e
        Wsw = vertex_switch(G, W, u)   # switch at u toggles all edges at u
        assert e not in Wsw, "e should have become non-wrap after switch"
        Gp, Wp = contract_edge_signed(G, Wsw, e)
        Gp, Wp = relabel(Gp, Wp)
        b1 = beta(G, W)   # β invariant under switching, so this is fine
        b2 = beta(Gp, Wp)
        ok = (b1 <= b2)
        c.record(ok, None if ok else {
            "claim": "A6'", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W),
            "e": list(e), "switched_at": u,
            "beta_G": b1, "beta_result": b2,
        })


# ---------------------------------------------------------------------------
# L15 cross-check.
# ---------------------------------------------------------------------------

def test_L15_forward(G, W, c, edge_cap=None):
    """β(G, W) ≤ β(G - e, W) for non-bridge non-wrap e."""
    br = bridges(G)
    edges = [e for e in edge_list(G) if e not in W and e not in br]
    if edge_cap is not None and len(edges) > edge_cap:
        edges = RNG.sample(edges, edge_cap)
    for e in edges:
        Gp = G.copy()
        Gp.remove_edge(*e)
        b1 = beta(G, W)
        b2 = beta(Gp, W)
        ok = (b1 <= b2)
        c.record(ok, None if ok else {
            "claim": "L15", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "e": list(e),
            "beta_G": b1, "beta_Ge": b2,
        })


def test_L15_reverse(G, W, c, edge_cap=None):
    """Reverse Lipschitz spot-check: β(G - e, W) ≤ β(G, W) + 1 for all e
    (non-bridge non-wrap, for parity with L15 regime)."""
    br = bridges(G)
    edges = [e for e in edge_list(G) if e not in W and e not in br]
    if edge_cap is not None and len(edges) > edge_cap:
        edges = RNG.sample(edges, edge_cap)
    for e in edges:
        Gp = G.copy()
        Gp.remove_edge(*e)
        b1 = beta(G, W)
        b2 = beta(Gp, W)
        ok = (b2 <= b1 + 1)
        c.record(ok, None if ok else {
            "claim": "L15-reverse", "n": G.number_of_nodes(),
            "edges": edge_list(G), "W": sorted(W), "e": list(e),
            "beta_G": b1, "beta_Ge": b2,
        })


# ---------------------------------------------------------------------------
# Small-n exhaustive exerciser.
# ---------------------------------------------------------------------------

def small_instances(n_min=3, n_max=5, only_connected=False):
    for n in range(n_min, n_max + 1):
        for G in all_labeled_graphs(n):
            if only_connected and (n >= 1) and not nx.is_connected(G):
                continue
            edges = edge_list(G)
            m = len(edges)
            if m == 0:
                yield n, G, frozenset()
                continue
            # exhaustive over W
            for mask in range(1 << m):
                W = frozenset(edges[i] for i in range(m) if mask & (1 << i))
                yield n, G, W


def enum_isomorphism_classes_n6(cap=120):
    """Return up to `cap` non-isomorphic connected graphs on 6 nodes using
    WL-hash dedup. Not perfect, but very fast."""
    seen = {}
    for G in all_labeled_graphs(6):
        if not nx.is_connected(G):
            continue
        h = nx.weisfeiler_lehman_graph_hash(G)
        if h not in seen:
            seen[h] = G
            if len(seen) >= cap:
                break
    return list(seen.values())


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------

def run_alpha_scale_n6(claims, target_graphs=N6_TARGET_CONNECTED_GRAPHS,
                      wraps=N6_WRAP_SAMPLES_PER_GRAPH):
    """Runs A2, A3, A8, A10, A12, A13 on n=6 labeled connected graph sample."""
    print(f"[α n=6 scale] sampling {target_graphs} connected graphs × "
          f"{wraps} wrap subsets each")
    t0 = time.time()
    graphs = sample_connected_n6_graphs(target_graphs)
    print(f"  got {len(graphs)} graphs in {time.time()-t0:.1f}s")
    for gi, G in enumerate(graphs):
        ws = list(random_wrap_subsets(G, wraps))
        for W in ws:
            test_A2(G, W, claims["A2"])
            test_A3(G, W, claims["A3"])
            test_A8(G, W, claims["A8"])
            test_A10(G, W, claims["A10"])
            test_A12(G, W, claims["A12"])
            test_A13(G, W, claims["A13"])
        if gi % 50 == 0:
            print(f"   progress: graph {gi}/{len(graphs)}, "
                  f"elapsed {time.time()-t0:.1f}s")


def run_alpha_small_exhaustive(claims, n_max=5):
    """Top-up at n ≤ 5: exhaustive on every (G, W)."""
    print(f"[α n≤{n_max} exhaustive] sweeping all labeled graphs, all W")
    t0 = time.time()
    k = 0
    for n, G, W in small_instances(n_min=3, n_max=n_max):
        if not nx.is_connected(G):
            # Pendant-addition claims still make sense on disconnected G;
            # tests A2/A3/A10/A13 are safe. A8/A12 we restrict to connected.
            test_A2(G, W, claims["A2"])
            test_A3(G, W, claims["A3"])
            test_A10(G, W, claims["A10"])
            test_A13(G, W, claims["A13"])
        else:
            test_A2(G, W, claims["A2"])
            test_A3(G, W, claims["A3"])
            test_A8(G, W, claims["A8"])
            test_A10(G, W, claims["A10"])
            test_A12(G, W, claims["A12"])
            test_A13(G, W, claims["A13"])
        k += 1
    print(f"  swept {k} (G, W) configs in {time.time()-t0:.1f}s")


def run_inequalities_small_exhaustive(claims, n_max=5):
    print(f"[ineq n≤{n_max} exhaustive] A5', A6', L15, L15-rev on connected G")
    t0 = time.time()
    k = 0
    for n, G, W in small_instances(n_min=3, n_max=n_max, only_connected=True):
        test_A5prime(G, W, claims["A5'"])
        test_A6prime(G, W, claims["A6'"])
        test_L15_forward(G, W, claims["L15"])
        test_L15_reverse(G, W, claims["L15_rev"])
        k += 1
    print(f"  swept {k} connected (G, W) configs in {time.time()-t0:.1f}s")


def run_inequalities_n6_sample(claims, sample=N6_INEQ_SAMPLE):
    print(f"[ineq n=6 random sample] target {sample} configs for A5'/A6'/L15")
    t0 = time.time()
    # strategy: sample random connected G6, random W, then iterate eligible e
    needed = sample
    count = 0
    while count < needed:
        G = random_connected_graph(6)
        # one random W
        m = G.number_of_edges()
        if m == 0:
            continue
        edges = edge_list(G)
        r = RNG.randint(0, m)
        W = frozenset(RNG.sample(edges, r)) if r > 0 else frozenset()
        test_A5prime(G, W, claims["A5'"], edge_cap=3)
        test_A6prime(G, W, claims["A6'"], edge_cap=3)
        test_L15_forward(G, W, claims["L15"], edge_cap=3)
        test_L15_reverse(G, W, claims["L15_rev"], edge_cap=3)
        count += 1
    print(f"  sampled {count} configs in {time.time()-t0:.1f}s")


def run_L15_n6_direct(claims, sample=L15_SAMPLE_N6):
    """Priority 3: spot-check L15 at n=6, ≥ 1000 configs."""
    print(f"[L15 n=6 direct] target {sample} configs")
    t0 = time.time()
    count = 0
    while count < sample:
        G = random_connected_graph(6)
        m = G.number_of_edges()
        if m == 0:
            continue
        edges = edge_list(G)
        r = RNG.randint(0, m)
        W = frozenset(RNG.sample(edges, r)) if r > 0 else frozenset()
        test_L15_forward(G, W, claims["L15"], edge_cap=3)
        test_L15_reverse(G, W, claims["L15_rev"], edge_cap=3)
        count += 1
    print(f"  sampled {count} configs in {time.time()-t0:.1f}s")


def main(out_json):
    t_start = time.time()

    claims = {
        "A2":       FuzzyClaim("A2",       "Pendant non-wrap add preserves β"),
        "A3":       FuzzyClaim("A3",       "Pendant wrap add preserves β"),
        "A8":       FuzzyClaim("A8",       "k-subdivision with parity-matching new wraps preserves β (k ∈ {2,3})"),
        "A10":      FuzzyClaim("A10",      "Add-2-edges order-independent for β"),
        "A12":      FuzzyClaim("A12",      "Theta-replacement of non-wrap edge preserves β"),
        "A13":      FuzzyClaim("A13",      "Vertex-switching invariance: β(G,W) = β(G, W △ δ(v))"),
        "A5'":      FuzzyClaim("A5'",      "β(G,W) ≤ β(G/e, W') for non-bridge non-wrap e"),
        "A6'":      FuzzyClaim("A6'",      "β(G,W) ≤ β(G/switched(e), W') for non-bridge wrap e"),
        "L15":      FuzzyClaim("L15",      "β(G,W) ≤ β(G−e, W) for non-bridge non-wrap e (cross-check)"),
        "L15_rev":  FuzzyClaim("L15-rev",  "β(G−e, W) ≤ β(G,W) + 1 (reverse Lipschitz bound)"),
    }

    run_alpha_small_exhaustive(claims, n_max=5)
    run_alpha_scale_n6(claims)
    run_inequalities_small_exhaustive(claims, n_max=5)
    run_inequalities_n6_sample(claims)
    run_L15_n6_direct(claims)

    elapsed = time.time() - t_start
    print(f"\nTotal elapsed: {elapsed:.1f}s")
    print("\nResults (ranked by τ then trials):")
    rows = [c.to_dict() for c in claims.values()]
    for r in sorted(rows, key=lambda r: (-r["tau"], -r["tested"])):
        print(f"  {r['key']:<10} τ={r['tau']:.4f}  "
              f"({r['passed']:>6}/{r['tested']:<7})  {r['name']}")

    Path(out_json).write_text(json.dumps(rows, indent=2, default=str))
    print(f"\nWrote {out_json}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).parent / "results.json")
    main(out)
