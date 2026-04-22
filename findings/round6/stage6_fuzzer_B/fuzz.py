"""FUZZER-B R6 Stage 6 — n=7 gap check on PROVER-B Tier-1 and β-Lipschitz bundle.

Stage 5 did n <= 5 exhaustive + n=6 sample; this tile pushes the critical
claims to n=7 random sample to catch any scale-dependent CE before PROVER-B
starts formalising.

Targets (priority order):
  S1: shifted-det factorisation     det(L_möb+αI) = det(L_s+αI)·det(L_sig+αI)
  S2: C10                            tr(L_s·L_sig) = tr(L_s^2) - 4|W|
  S3: C11                            tr(L_möb^2) = tr(L_s^2) + tr(L_sig^2)
  S4: C12                            ||L_möb||_F^2 = ||L_s||_F^2 + ||L_sig||_F^2
  S6: C5                             |β(G) - β(G/e)| <= 1 for non-bridge e
  S7: C6-tight                       |β(G) - β(G-v)| <= max(1, deg(v))
  S8: C13                            bridge-wrap-flip preserves β
  S9: C14                            non-bridge-wrap-flip |Δβ| <= 1
"""
from __future__ import annotations
import random, time, json, sys
import numpy as np
import networkx as nx
from itertools import combinations

RNG = random.Random(20260501)

def random_connected(n, p_low=0.2, p_high=0.85, tries=500):
    for _ in range(tries):
        p = RNG.uniform(p_low, p_high)
        G = nx.gnp_random_graph(n, p, seed=RNG.randint(0, 1<<30))
        if nx.is_connected(G):
            return G
    # fallback: path
    return nx.path_graph(n)

def edges_sorted(G):
    return [tuple(sorted(e)) for e in G.edges()]

def beta(G, W):
    total = 0
    for comp in nx.connected_components(G):
        sub = G.subgraph(comp)
        color = {}
        bal = True
        for root in sub.nodes():
            if root in color: continue
            color[root] = 0
            stack = [root]
            while stack:
                u = stack.pop()
                for w in sub.neighbors(u):
                    e = tuple(sorted((u, w)))
                    flip = 1 if e in W else 0
                    need = color[u] ^ flip
                    if w in color:
                        if color[w] != need:
                            bal = False
                            break
                    else:
                        color[w] = need
                        stack.append(w)
                if not bal: break
            if not bal: break
        if bal: total += 1
    return total

def build_laplacians(G, W):
    """Return (L_scalar (n×n), L_signed (n×n), L_mob (2n×2n))."""
    n = G.number_of_nodes()
    L_s = np.zeros((n, n))
    L_sig = np.zeros((n, n))
    L_m = np.zeros((2*n, 2*n))
    for u, v in G.edges():
        e = tuple(sorted((u, v)))
        L_s[u, u] += 1; L_s[v, v] += 1
        L_s[u, v] -= 1; L_s[v, u] -= 1
        L_sig[u, u] += 1; L_sig[v, v] += 1
        if e in W:
            L_sig[u, v] += 1; L_sig[v, u] += 1
        else:
            L_sig[u, v] -= 1; L_sig[v, u] -= 1
        # L_möb: 2n × 2n, fibre = Fin 2
        # Non-wrap: couples (u,0)-(v,0) and (u,1)-(v,1) with -1 each
        # Wrap: couples (u,0)-(v,1) and (u,1)-(v,0) with -1 each
        # Diagonal (u,i) += 1 per incident edge
        for i in (0, 1):
            L_m[2*u+i, 2*u+i] += 1
            L_m[2*v+i, 2*v+i] += 1
        if e in W:
            L_m[2*u+0, 2*v+1] -= 1; L_m[2*v+1, 2*u+0] -= 1
            L_m[2*u+1, 2*v+0] -= 1; L_m[2*v+0, 2*u+1] -= 1
        else:
            L_m[2*u+0, 2*v+0] -= 1; L_m[2*v+0, 2*u+0] -= 1
            L_m[2*u+1, 2*v+1] -= 1; L_m[2*v+1, 2*u+1] -= 1
    return L_s, L_sig, L_m

def contract_edge(G, W, e):
    """Contract e=(u,v). Returns (G', W') with u merged into v."""
    u, v = e
    Gp = nx.Graph()
    Gp.add_nodes_from(x for x in G.nodes() if x != u)
    Wp = set()
    for a, b in G.edges():
        if (a, b) == (u, v) or (a, b) == (v, u): continue
        na = v if a == u else a
        nb = v if b == u else b
        if na == nb: continue
        ee = tuple(sorted((na, nb)))
        if ee in Gp.edges():
            continue
        Gp.add_edge(*ee)
        old = tuple(sorted((a, b)))
        if old in W:
            Wp.add(ee)
    return Gp, Wp

def is_bridge(G, e):
    bridges = set(tuple(sorted(b)) for b in nx.bridges(G))
    return tuple(sorted(e)) in bridges

def fuzz_all(n_list=(7,), per_n=300):
    stats = {k: {'tested':0,'passed':0,'ces':[],'max_diff':0.0}
             for k in ('S1_a1','S1_a2','S2','S3','S4','S6','S7','S8','S9')}

    t0 = time.time()
    for n in n_list:
        for g_idx in range(per_n):
            G = random_connected(n)
            edges = edges_sorted(G)
            m = len(edges)
            if m == 0: continue
            # random W
            W = frozenset(edges[i] for i in range(m) if RNG.random() < 0.5)
            L_s, L_sig, L_m = build_laplacians(G, W)

            # S1: det(L + αI) factorisation
            for alpha_key, alpha in (('S1_a1', 1.0), ('S1_a2', 2.5)):
                lhs = np.linalg.det(L_m + alpha * np.eye(2*n))
                rhs = np.linalg.det(L_s + alpha*np.eye(n)) * np.linalg.det(L_sig + alpha*np.eye(n))
                d = abs(lhs - rhs) / max(1e-30, abs(lhs))
                stats[alpha_key]['tested'] += 1
                if d < 1e-7:
                    stats[alpha_key]['passed'] += 1
                else:
                    if len(stats[alpha_key]['ces']) < 3:
                        stats[alpha_key]['ces'].append({'n':n,'edges':list(edges),'W':list(W),'alpha':alpha,'lhs':lhs,'rhs':rhs,'rel':d})
                stats[alpha_key]['max_diff'] = max(stats[alpha_key]['max_diff'], d)

            # S2: tr(L_s·L_sig) = tr(L_s²) - 4|W|
            lhs_s2 = np.trace(L_s @ L_sig)
            rhs_s2 = np.trace(L_s @ L_s) - 4*len(W)
            d_s2 = abs(lhs_s2 - rhs_s2)
            stats['S2']['tested'] += 1
            if d_s2 < 1e-8:
                stats['S2']['passed'] += 1
            else:
                if len(stats['S2']['ces']) < 3:
                    stats['S2']['ces'].append({'n':n,'edges':list(edges),'W':list(W),'lhs':lhs_s2,'rhs':rhs_s2})
            stats['S2']['max_diff'] = max(stats['S2']['max_diff'], d_s2)

            # S3: tr(L_möb²) = tr(L_s²) + tr(L_sig²)
            lhs3 = np.trace(L_m @ L_m)
            rhs3 = np.trace(L_s @ L_s) + np.trace(L_sig @ L_sig)
            d3 = abs(lhs3 - rhs3)
            stats['S3']['tested'] += 1
            if d3 < 1e-8: stats['S3']['passed'] += 1
            stats['S3']['max_diff'] = max(stats['S3']['max_diff'], d3)

            # S4: Frobenius
            lhs4 = np.sum(L_m**2)
            rhs4 = np.sum(L_s**2) + np.sum(L_sig**2)
            d4 = abs(lhs4 - rhs4)
            stats['S4']['tested'] += 1
            if d4 < 1e-8: stats['S4']['passed'] += 1
            stats['S4']['max_diff'] = max(stats['S4']['max_diff'], d4)

            # S6: contraction-Lipschitz (non-bridge edges)
            b0 = beta(G, W)
            for e in edges:
                if is_bridge(G, e): continue
                Gc, Wc = contract_edge(G, W, e)
                b1 = beta(Gc, Wc)
                stats['S6']['tested'] += 1
                if abs(b0 - b1) <= 1:
                    stats['S6']['passed'] += 1
                else:
                    if len(stats['S6']['ces']) < 4:
                        stats['S6']['ces'].append({'n':n,'edges':list(edges),'W':list(W),'e':list(e),'b0':b0,'b1':b1})

            # S7: vertex-deletion with max(1, deg)
            for v in list(G.nodes()):
                Gv = G.copy(); Gv.remove_node(v)
                Wv = frozenset(e for e in W if v not in e)
                bv = beta(Gv, Wv)
                stats['S7']['tested'] += 1
                bound = max(1, G.degree(v))
                if abs(b0 - bv) <= bound:
                    stats['S7']['passed'] += 1
                else:
                    if len(stats['S7']['ces']) < 4:
                        stats['S7']['ces'].append({'n':n,'edges':list(edges),'W':list(W),'v':v,'deg':G.degree(v),'b0':b0,'bv':bv})

            # S8: bridge-wrap-flip preserves β
            for e in edges:
                if not is_bridge(G, e): continue
                Wflip = set(W)
                if e in Wflip: Wflip.remove(e)
                else: Wflip.add(e)
                b1 = beta(G, frozenset(Wflip))
                stats['S8']['tested'] += 1
                if b0 == b1: stats['S8']['passed'] += 1
                else:
                    if len(stats['S8']['ces']) < 4:
                        stats['S8']['ces'].append({'n':n,'edges':list(edges),'W':list(W),'bridge':list(e),'b0':b0,'b1':b1})

            # S9: non-bridge wrap-flip |Δβ| ≤ 1
            for e in edges:
                if is_bridge(G, e): continue
                Wflip = set(W)
                if e in Wflip: Wflip.remove(e)
                else: Wflip.add(e)
                b1 = beta(G, frozenset(Wflip))
                stats['S9']['tested'] += 1
                if abs(b0 - b1) <= 1: stats['S9']['passed'] += 1
                else:
                    if len(stats['S9']['ces']) < 4:
                        stats['S9']['ces'].append({'n':n,'edges':list(edges),'W':list(W),'e':list(e),'b0':b0,'b1':b1})

    elapsed = time.time() - t0
    print(f"[stage6 n={n_list[0]} per_n={per_n}] elapsed={elapsed:.1f}s")
    print()
    print(f"{'claim':<8} {'tested':>8} {'passed':>8}  {'max_err':>12}   verdict")
    print("-" * 55)
    for k, v in stats.items():
        ok = v['passed'] == v['tested']
        verdict = 'HOLDS' if ok else f"FAIL ({len(v['ces'])} CEs)"
        print(f"{k:<8} {v['tested']:>8} {v['passed']:>8}  {v['max_diff']:>12.3e}   {verdict}")
        for ce in v['ces'][:2]:
            print('  CE:', ce)
    # dump
    with open('results.json','w') as f:
        json.dump(stats, f, indent=2, default=str)
    print('[wrote results.json]')

if __name__ == '__main__':
    fuzz_all(n_list=(7,), per_n=300)
