"""
NEGATOR-A Round 6 — sheaf-section alpha (edge operations).

Generates & fuzz-scores 12 NEW claims about edge-level operations on
connection graphs (G, W):

  A1  Wrap-preserving deletion: removing a non-bridge edge e preserves
      beta whenever the wrap parity of e is unchanged on the cycle space
      (equivalent here: e not in W AND e non-bridge AND G connected).
  A2  Bridge-wrap insertion: adding a new bridge edge with ANY wrap state
      increments the number of components by -1 and keeps beta the same
      (beta is additive on disjoint union + bridge-wrap gets absorbed).
      Claim here: beta(G + bridge e, W) = beta(G, W) for non-wrap e.
  A3  Bridge-wrap insertion, wrap case: beta(G + bridge e, W + {e})
      == beta(G, W).
      (Adding a bridge — wrap or non-wrap — cannot change number of
      balanced components.)
  A4  Edge-swap invariance (deg-preserving, wrap-preserving swap):
      if e, e' both non-wrap, non-bridge, and removing e then adding e'
      preserves (G connected), then beta unchanged.
  A5  Contracting a non-bridge non-wrap edge preserves beta.
      (R4 C1 direction; contrasts with R5 R8 which is bridge-only.)
  A6  Contracting a wrap edge: beta(G / e, W_{switch-v}) == beta(G, W)
      where switch at one endpoint v of e is applied before contraction.
      Equivalently: contracting a wrap edge with pre-switch preserves beta.
  A7  Iterated subdivision k times (all new edges non-wrap) on a non-wrap
      edge preserves beta.  (extends R5 R6 k=1.)
  A8  Wrap-to-non-wrap subdivision conversion: subdividing a wrap edge into
      k parts with even number of wraps preserves beta.
  A9  Add 2 disjoint non-wrap edges = identity on beta vs
      add 1 wrap edge: both commute with beta up to non-wrap case
      (beta unchanged for 2 non-wrap adds on non-bridges; general status
      tested).
  A10 Multi-edge add commutator: (add e1, then add e2) gives the same
      beta as (add e2, then add e1).
  A11 Edge-set complement on a bipartite-wrap subgraph: if W itself is
      bipartite (as a graph on V), beta(G, W) == beta(G, E \\ W)?
      (Narrower than R4 where G is bipartite.)
  A12 Double-edge subdivision: replace e by two parallel paths of length
      2 (equivalently, subdivide twice and keep as a theta-graph) — beta
      preserved iff the two new paths have equal wrap-parity.

For each claim tau(C) = |supp| / |pre|.

Writes results.json next to this script.
"""

from __future__ import annotations

import itertools
import json
import math
import random
import sys
from pathlib import Path

import networkx as nx
import numpy as np


TOL = 1e-8
RNG = random.Random(20260422)


# ---------------------------------------------------------------------------
# Laplacian / beta helpers (copy of R5 utilities).
# ---------------------------------------------------------------------------

def edge_list(G):
    return [tuple(sorted(e)) for e in G.edges()]


def is_balanced_component(G, wrap):
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
    return balanced_component_count(G, wrap)


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


def bridges(G):
    return set(tuple(sorted(e)) for e in nx.bridges(G))


def relabel(G, W):
    mapping = {old: new for new, old in enumerate(sorted(G.nodes()))}
    Gr = nx.relabel_nodes(G, mapping)
    Wr = frozenset(tuple(sorted((mapping[a], mapping[b])))
                   for (a, b) in W
                   if a in mapping and b in mapping)
    return Gr, Wr


def describe(G, W):
    return {"n": G.number_of_nodes(),
            "edges": edge_list(G),
            "wrap": sorted(list(W))}


def small_instances(n_min=3, n_max=5):
    for n in range(n_min, n_max + 1):
        for G in all_graphs_iso(n):
            for W in all_wrap_subsets(G):
                yield n, G, W


def n6_sample_instances(n=6, graphs_cap=12, wrap_cap=16):
    graphs = all_graphs_iso(n)
    # retain a sample of at most graphs_cap iso classes
    if len(graphs) > graphs_cap:
        graphs = RNG.sample(graphs, graphs_cap)
    for G in graphs:
        subs = list(all_wrap_subsets(G))
        if len(subs) > wrap_cap:
            subs = RNG.sample(subs, wrap_cap)
        for W in subs:
            yield n, G, W


# ---------------------------------------------------------------------------
# Fuzzy claim container.
# ---------------------------------------------------------------------------

class FuzzyClaim:
    def __init__(self, idx, name, hypothesis=""):
        self.idx = idx
        self.name = name
        self.hypothesis = hypothesis
        self.tested = 0
        self.passed = 0
        self.counterexample = None
        self.sample_supports = []  # up to 60

    def record(self, ok, ce=None, support=None):
        self.tested += 1
        if ok:
            self.passed += 1
            if support is not None and len(self.sample_supports) < 60:
                self.sample_supports.append(support)
        elif self.counterexample is None:
            self.counterexample = ce

    @property
    def tau(self):
        return 0.0 if self.tested == 0 else self.passed / self.tested

    def verdict(self):
        t = self.tau
        if t == 1.0:
            return f"TRUE (fuzz-verified tau=1.0000, n={self.tested})"
        if t > 0.9:
            return f"NEAR-TRUE (tau={t:.4f})"
        if t > 0.5:
            return f"MOSTLY TRUE (tau={t:.4f})"
        if t > 0.1:
            return f"MIXED (tau={t:.4f})"
        return f"COUNTEREXAMPLE-RICH (tau={t:.4f})"

    def to_dict(self):
        return {
            "idx": self.idx,
            "name": self.name,
            "hypothesis": self.hypothesis,
            "tested": self.tested,
            "passed": self.passed,
            "tau": round(self.tau, 6),
            "verdict": self.verdict(),
            "counterexample": self.counterexample,
            "sample_supports": self.sample_supports[:60],
        }


# ---------------------------------------------------------------------------
# Claim A1: wrap-preserving deletion (non-bridge non-wrap) — restated from
# R5-R2 as a cross-check with a slightly different hypothesis (preserves
# beta in both directions, G possibly disconnected).
# ---------------------------------------------------------------------------

def claim_a1_nonbridge_nonwrap_delete():
    c = FuzzyClaim("A1", "beta(G,W) == beta(G-e,W) for non-bridge non-wrap e (any G)",
                   "e not a bridge of G, e not in W")
    for n, G, W in small_instances():
        br = bridges(G)
        for e in edge_list(G):
            if e in W or e in br:
                continue
            Ge = G.copy()
            Ge.remove_edge(*e)
            b1 = beta(G, W)
            b2 = beta(Ge, W)
            supp = {"n": n, "m": G.number_of_edges(), "e": list(e),
                    "beta_G": b1, "beta_Ge": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "removed_edge": list(e),
                                 "beta_G": b1, "beta_Ge": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A2: adding a new pendant edge (bridge) with NON-wrap status does
# not change beta.
# Setup: pick a vertex v of G, add a new vertex w (fresh label),
# add edge (v,w) as a non-wrap bridge. Verify beta(G',W) == beta(G,W) + 1
# (because the new singleton-merged component is trivially balanced).
# Actually: the new extended component is balanced iff the original
# component containing v was balanced. So beta doesn't change.
# We test: beta(G', W) == beta(G, W).
# ---------------------------------------------------------------------------

def claim_a2_bridge_add_nonwrap():
    c = FuzzyClaim("A2", "Adding a pendant non-wrap edge preserves beta",
                   "new vertex w, new edge (v, w) not in W")
    for n, G, W in small_instances():
        for v in G.nodes():
            Gp = G.copy()
            w = n  # fresh
            Gp.add_node(w)
            Gp.add_edge(v, w)
            Wp = frozenset(W)
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            supp = {"n": n, "v": v, "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "attached_vertex": v,
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A3: adding a pendant wrap edge also preserves beta.
# Same setup but mark the new edge as wrap.
# ---------------------------------------------------------------------------

def claim_a3_bridge_add_wrap():
    c = FuzzyClaim("A3", "Adding a pendant wrap edge preserves beta",
                   "new vertex w, new edge (v, w) in W")
    for n, G, W in small_instances():
        for v in G.nodes():
            Gp = G.copy()
            w = n
            Gp.add_node(w)
            new_e = tuple(sorted((v, w)))
            Gp.add_edge(*new_e)
            Wp = frozenset(set(W) | {new_e})
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            supp = {"n": n, "v": v, "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "attached_vertex": v,
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A4: non-wrap edge swap preserving connectivity preserves beta.
#   Precondition: e and e' both non-wrap, e in E(G), e' not in E(G),
#   both non-bridge after respective modifications, and G remains connected.
#   Operation: remove e, add e'.
# ---------------------------------------------------------------------------

def claim_a4_nonwrap_edge_swap():
    c = FuzzyClaim("A4", "Non-wrap edge swap (remove e, add e') preserves beta when e, e' both non-wrap non-bridge and connectivity preserved",
                   "G connected; e in E\\W non-bridge; e' not in E; connected after swap; e' not in W; e' not a bridge of result")
    for n, G, W in small_instances():
        if not nx.is_connected(G):
            continue
        br = bridges(G)
        edges = edge_list(G)
        V = list(G.nodes())
        all_pairs = [tuple(sorted((u, v))) for u, v in itertools.combinations(V, 2)]
        non_edges = [p for p in all_pairs if p not in set(edges)]
        for e in edges:
            if e in W or e in br:
                continue
            for ep in non_edges:
                if ep in W:
                    continue
                Gp = G.copy()
                Gp.remove_edge(*e)
                Gp.add_edge(*ep)
                if not nx.is_connected(Gp):
                    continue
                # ep should be non-bridge in Gp
                br_new = bridges(Gp)
                if ep in br_new:
                    continue
                b1 = beta(G, W)
                b2 = beta(Gp, W)
                supp = {"n": n, "e": list(e), "ep": list(ep),
                        "beta_G": b1, "beta_Gp": b2}
                ok = (b1 == b2)
                if not ok:
                    c.record(False, {**describe(G, W),
                                     "removed_edge": list(e),
                                     "added_edge": list(ep),
                                     "beta_G": b1, "beta_Gp": b2})
                else:
                    c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A5: contracting a non-bridge non-wrap edge preserves beta.
#   (R4 C1 direction; R5 R8 handled the bridge case.)
# ---------------------------------------------------------------------------

def contract_edge(G, W, e):
    u, v = e
    Gp = G.copy()
    Gp = nx.contracted_edge(Gp, (u, v), self_loops=False)
    # v merged into u: remove any edges that collapse.
    Wp = set()
    for a, b in W:
        if (a, b) == e or (b, a) == e:
            continue  # contracted edge itself vanishes
        a2 = u if a == v else a
        b2 = u if b == v else b
        if a2 != b2:
            Wp.add(tuple(sorted((a2, b2))))
    return Gp, frozenset(Wp)


def claim_a5_nonbridge_nonwrap_contract():
    c = FuzzyClaim("A5", "Contracting a non-bridge non-wrap edge preserves beta",
                   "e non-bridge, e not in W, G connected")
    for n, G, W in small_instances():
        if n > 5:
            break
        if not nx.is_connected(G):
            continue
        br = bridges(G)
        for e in edge_list(G):
            if e in W or e in br:
                continue
            Gp, Wp = contract_edge(G, W, e)
            Gp, Wp = relabel(Gp, Wp)
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            supp = {"n": n, "e": list(e), "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "contracted": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A6: contracting a wrap edge, after switching at one endpoint v,
# preserves beta.
#   switch_v(W) = W xor star(v).
# ---------------------------------------------------------------------------

def vertex_switch(G, W, v):
    new_W = set(W)
    for u in G.neighbors(v):
        e = tuple(sorted((u, v)))
        if e in new_W:
            new_W.discard(e)
        else:
            new_W.add(e)
    return frozenset(new_W)


def claim_a6_wrap_contract_with_switch():
    c = FuzzyClaim("A6", "Contract wrap edge e after switching at one endpoint preserves beta",
                   "e in W; W' = switch_v(W) for v an endpoint of e; then e becomes non-wrap, contract")
    for n, G, W in small_instances():
        if n > 5:
            break
        if not nx.is_connected(G):
            continue
        for e in edge_list(G):
            if e not in W:
                continue
            u, v = e
            Wsw = vertex_switch(G, W, v)
            # After switching, e should now be NOT in Wsw (since it was in W).
            # Contract e (now non-wrap).
            Gp, Wp = contract_edge(G, Wsw, e)
            Gp, Wp = relabel(Gp, Wp)
            # Switching preserves balance class ⇒ beta(G, W) == beta(G, Wsw).
            # And contracting a non-wrap edge... is in principle beta-preserving
            # only when it is a bridge (R8). For a non-bridge wrap contraction,
            # we predict NOT generally preserving. We state the claim anyway
            # and measure tau: this is the "switching-contraction" duality
            # candidate.
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            supp = {"n": n, "e": list(e), "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "contracted": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A7: iterated k-fold subdivision of a non-wrap edge preserves beta,
# for k in {2, 3}. All new edges non-wrap.
# ---------------------------------------------------------------------------

def subdivide_edge_k_nonwrap(G, e, k, base_label):
    """Replace edge (u,v) by path u - w_1 - w_2 - ... - w_k - v with k
    fresh vertices all non-wrap edges. Returns new graph and vertex list."""
    u, v = e
    Gp = G.copy()
    new_nodes = [base_label + i for i in range(k)]
    Gp.remove_edge(u, v)
    for w in new_nodes:
        Gp.add_node(w)
    chain = [u] + new_nodes + [v]
    for a, b in zip(chain, chain[1:]):
        Gp.add_edge(a, b)
    return Gp


def claim_a7_iterated_subdivision_nonwrap():
    c = FuzzyClaim("A7", "Iterated k-fold subdivision of non-wrap edge preserves beta for k in {2,3}",
                   "e not in W; k fresh vertices inserted, all new edges non-wrap")
    for n, G, W in small_instances(n_max=4):
        for e in edge_list(G):
            if e in W:
                continue
            for k in (2, 3):
                Gp = subdivide_edge_k_nonwrap(G, e, k, base_label=n)
                Wp = frozenset(W)  # unchanged (new edges non-wrap)
                b1 = beta(G, W)
                b2 = beta(Gp, Wp)
                supp = {"n": n, "e": list(e), "k": k,
                        "beta_G": b1, "beta_Gp": b2}
                ok = (b1 == b2)
                if not ok:
                    c.record(False, {**describe(G, W), "subdivided": list(e),
                                     "k": k, "beta_G": b1, "beta_Gp": b2})
                else:
                    c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A8: subdividing a wrap edge into k parts with an EVEN number of
# wrap edges among the k new edges preserves beta.
# (Parity of cycle-wrap count is unchanged iff even flip.)
# ---------------------------------------------------------------------------

def subdivide_edge_with_wrap_mask(G, W, e, mask_bits, base_label):
    """mask_bits[i] = 1 iff new edge i is wrap.  Length k = len(mask_bits)."""
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


def claim_a8_wrap_subdivide_even_wrap_count():
    c = FuzzyClaim("A8", "Subdividing edge e (wrap or non-wrap) into k parts s.t. new-wrap-count has same parity as [e in W] preserves beta",
                   "k in {2,3}; new wrap parity matches old wrap parity on e")
    for n, G, W in small_instances(n_max=4):
        for e in edge_list(G):
            orig_parity = 1 if e in W else 0
            for k in (2, 3):
                for mask in range(1 << k):
                    bits = [(mask >> i) & 1 for i in range(k)]
                    if sum(bits) % 2 != orig_parity:
                        continue
                    Gp, Wp = subdivide_edge_with_wrap_mask(G, W, e, bits, base_label=n)
                    b1 = beta(G, W)
                    b2 = beta(Gp, Wp)
                    supp = {"n": n, "e": list(e), "k": k,
                            "mask": bits, "beta_G": b1, "beta_Gp": b2}
                    ok = (b1 == b2)
                    if not ok:
                        c.record(False, {**describe(G, W), "subdivided": list(e),
                                         "k": k, "mask": bits,
                                         "beta_G": b1, "beta_Gp": b2})
                    else:
                        c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A9: Adding two disjoint non-wrap edges vs. adding one wrap edge:
#   beta(G + e1 + e2, W) = beta(G, W) when e1, e2 are new non-wrap edges.
# ---------------------------------------------------------------------------

def claim_a9_add_two_nonwrap():
    c = FuzzyClaim("A9", "Adding 2 new non-wrap edges to G preserves beta",
                   "e1, e2 not in E(G); both non-wrap; e1 != e2")
    for n, G, W in small_instances(n_max=4):
        edges = set(edge_list(G))
        V = list(G.nodes())
        all_pairs = [tuple(sorted((u, v))) for u, v in itertools.combinations(V, 2)]
        non_edges = [p for p in all_pairs if p not in edges]
        count = 0
        for e1, e2 in itertools.combinations(non_edges, 2):
            count += 1
            if count > 10:
                break
            Gp = G.copy()
            Gp.add_edge(*e1)
            Gp.add_edge(*e2)
            b1 = beta(G, W)
            b2 = beta(Gp, W)
            supp = {"n": n, "e1": list(e1), "e2": list(e2),
                    "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "e1": list(e1), "e2": list(e2),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A10: multi-edge-add commutator triviality.
#   beta(G + e1 + e2, W + Wadd1 + Wadd2) == beta(G + e2 + e1, W + Wadd2 + Wadd1).
# Trivial by commutativity of set union. We test that the *procedural
# results* agree (this would only fail if our code had an order bug).
# ---------------------------------------------------------------------------

def claim_a10_add_commutator():
    c = FuzzyClaim("A10", "Order of adding 2 edges is irrelevant for beta",
                   "e1, e2 not in E(G), any wrap assignment; add in either order")
    for n, G, W in small_instances(n_max=4):
        edges = set(edge_list(G))
        V = list(G.nodes())
        all_pairs = [tuple(sorted((u, v))) for u, v in itertools.combinations(V, 2)]
        non_edges = [p for p in all_pairs if p not in edges]
        if len(non_edges) < 2:
            continue
        for _ in range(6):
            e1, e2 = RNG.sample(non_edges, 2)
            for w_flags in itertools.product((0, 1), repeat=2):
                G1 = G.copy(); G1.add_edge(*e1); G1.add_edge(*e2)
                G2 = G.copy(); G2.add_edge(*e2); G2.add_edge(*e1)
                W_new = set(W)
                if w_flags[0]:
                    W_new.add(e1)
                if w_flags[1]:
                    W_new.add(e2)
                W_new = frozenset(W_new)
                b1 = beta(G1, W_new)
                b2 = beta(G2, W_new)
                ok = (b1 == b2)
                supp = {"n": n, "e1": list(e1), "e2": list(e2),
                        "w_flags": w_flags, "beta": b1}
                if not ok:
                    c.record(False, {**describe(G, W), "e1": list(e1),
                                     "e2": list(e2), "wflags": w_flags,
                                     "b1": b1, "b2": b2})
                else:
                    c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A11: if the wrap-subgraph (V, W) is itself bipartite, does
# beta(G, W) == beta(G, E \ W)?
# (Narrower hypothesis than R5-R4 which required G bipartite.)
# ---------------------------------------------------------------------------

def is_W_bipartite(G, W):
    H = nx.Graph()
    H.add_nodes_from(G.nodes())
    H.add_edges_from(W)
    return nx.is_bipartite(H)


def claim_a11_W_bipartite_complement():
    c = FuzzyClaim("A11", "W bipartite (as a graph on V) implies beta(G,W) == beta(G, E\\W)",
                   "H=(V,W) is bipartite")
    for n, G, W in small_instances():
        if not is_W_bipartite(G, W):
            continue
        all_E = frozenset(edge_list(G))
        Wc = all_E - W
        b1 = beta(G, W)
        b2 = beta(G, Wc)
        supp = {"n": n, "m": G.number_of_edges(),
                "|W|": len(W), "beta_W": b1, "beta_Ec": b2}
        ok = (b1 == b2)
        if not ok:
            c.record(False, {**describe(G, W), "beta_W": b1, "beta_Ec": b2,
                             "Ec": sorted(Wc)})
        else:
            c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A12: double-edge subdivision (theta-replacement): replace edge e=(u,v)
# by TWO internally-disjoint paths of length 2 between u and v (via fresh
# vertices w1, w2). New edges are non-wrap.
# We claim: beta preserved iff the two new paths have equal wrap-parity.
# Here all new edges non-wrap, so wrap parities of the two paths are both 0
# => equal => beta preserved if e was non-wrap; otherwise replacing a wrap
# edge by two non-wrap paths of length 2 changes the fundamental cycle parity
# (adds a 4-cycle of all non-wrap through u-w1-v-w2-u).
# Claim (narrow): when e was non-wrap, beta is preserved. When e was wrap,
# we predict beta may change (test separately).
# ---------------------------------------------------------------------------

def theta_replace(G, W, e, base_label):
    u, v = e
    Gp = G.copy()
    Gp.remove_edge(u, v)
    w1 = base_label
    w2 = base_label + 1
    Gp.add_node(w1)
    Gp.add_node(w2)
    Gp.add_edge(u, w1); Gp.add_edge(w1, v)
    Gp.add_edge(u, w2); Gp.add_edge(w2, v)
    Wp = set(W)
    Wp.discard(e)
    return Gp, frozenset(Wp)


def claim_a12_theta_replace_nonwrap():
    c = FuzzyClaim("A12", "Theta-replacement of a NON-wrap edge by two non-wrap length-2 paths preserves beta",
                   "e not in W; replace by 2 parallel length-2 paths via fresh w1, w2, all new edges non-wrap")
    for n, G, W in small_instances(n_max=4):
        for e in edge_list(G):
            if e in W:
                continue
            Gp, Wp = theta_replace(G, W, e, base_label=n)
            b1 = beta(G, W)
            b2 = beta(Gp, Wp)
            supp = {"n": n, "e": list(e), "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "e": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A13 (bonus): beta is invariant under vertex switching on W.
#   beta(G, W) == beta(G, switch_v(W)).
# (Well-known for signed graphs; restated for the cover-Laplacian.)
# ---------------------------------------------------------------------------

def claim_a13_switching_invariance():
    c = FuzzyClaim("A13", "beta(G, W) == beta(G, switch_v W) for any vertex v",
                   "vertex-switching invariance")
    for n, G, W in small_instances():
        for v in G.nodes():
            Wsw = vertex_switch(G, W, v)
            b1 = beta(G, W)
            b2 = beta(G, Wsw)
            supp = {"n": n, "v": v, "beta": b1}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "v": v, "b1": b1, "b2": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Claim A14 (bonus): swap a wrap edge to a non-wrap edge by switching
# at either endpoint; beta unchanged. (Variation of A4.)
# More specifically: if e in W is not a bridge, let W' = W \ {e} (make e
# non-wrap). Then beta(G, W) vs beta(G, W') may or may not agree; it
# agrees iff the fundamental cycle through e was "even-wrapped".
# We measure this tau as a diagnostic.
# ---------------------------------------------------------------------------

def claim_a14_flip_single_edge_wrap():
    c = FuzzyClaim("A14", "Flipping wrap status of a single non-bridge edge preserves beta",
                   "e non-bridge; W' = W XOR {e}")
    for n, G, W in small_instances():
        br = bridges(G)
        for e in edge_list(G):
            if e in br:
                continue
            Wp = set(W)
            if e in Wp:
                Wp.discard(e)
            else:
                Wp.add(e)
            Wp = frozenset(Wp)
            b1 = beta(G, W)
            b2 = beta(G, Wp)
            supp = {"n": n, "e": list(e), "was_wrap": e in W,
                    "beta_G": b1, "beta_Gp": b2}
            ok = (b1 == b2)
            if not ok:
                c.record(False, {**describe(G, W), "e": list(e),
                                 "beta_G": b1, "beta_Gp": b2})
            else:
                c.record(True, support=supp)
    return c


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------

CLAIM_FNS = [
    claim_a1_nonbridge_nonwrap_delete,
    claim_a2_bridge_add_nonwrap,
    claim_a3_bridge_add_wrap,
    claim_a4_nonwrap_edge_swap,
    claim_a5_nonbridge_nonwrap_contract,
    claim_a6_wrap_contract_with_switch,
    claim_a7_iterated_subdivision_nonwrap,
    claim_a8_wrap_subdivide_even_wrap_count,
    claim_a9_add_two_nonwrap,
    claim_a10_add_commutator,
    claim_a11_W_bipartite_complement,
    claim_a12_theta_replace_nonwrap,
    claim_a13_switching_invariance,
    claim_a14_flip_single_edge_wrap,
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
    for r in sorted(results, key=lambda r: (-r["tau"], str(r["idx"]))):
        print(f"  {r['idx']:>3}  tau={r['tau']:.4f}  ({r['passed']}/{r['tested']:>5})  {r['name']}")


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else str(
        Path(__file__).parent / "results.json")
    main(out)
