"""Quick probe: does β(G/e, W') ≤ β(G, W) hold?  (Reverse of Stage-1 A5'.)

Reuses fuzz.py helpers.  If τ=1 here, promote as A5''/A6'' to PROVER-A queue.
"""
from __future__ import annotations
import sys, random, time
import networkx as nx
sys.path.insert(0, '.')
import fuzz

RNG = random.Random(20260429)

def is_bridge(G, e):
    return tuple(sorted(e)) in set(tuple(sorted(b)) for b in nx.bridges(G))

def switch_at(G, W, u):
    Wn = set(W)
    for v in G.neighbors(u):
        e = tuple(sorted((u,v)))
        if e in Wn: Wn.remove(e)
        else: Wn.add(e)
    return Wn

def probe(n_max=5, n6_sample=3000):
    print("[probe-reverse] A5'' candidate: beta(G/e, W') <= beta(G, W)")
    results_A5r = {'passed': 0, 'tested': 0, 'ces': []}
    results_A6r = {'passed': 0, 'tested': 0, 'ces': []}

    # n <= 5 exhaustive over labeled connected
    for n in range(3, n_max+1):
        for G in fuzz.all_labeled_graphs(n):
            if not nx.is_connected(G):
                continue
            edges = fuzz.edge_list(G)
            m = len(edges)
            if m == 0: continue
            for Wmask in range(1 << m):
                W = {edges[i] for i in range(m) if (Wmask >> i) & 1}
                for e in edges:
                    if is_bridge(G, e): continue
                    if e not in W:
                        Gc, Wc = fuzz.contract_edge_signed(G, W, e)
                        b0 = fuzz.beta(G, W); b1 = fuzz.beta(Gc, Wc)
                        results_A5r['tested'] += 1
                        if b1 <= b0:
                            results_A5r['passed'] += 1
                        elif len(results_A5r['ces']) < 4:
                            results_A5r['ces'].append({'n':n,'edges':[list(x) for x in edges],'W':[list(x) for x in W],'e':list(e),'beta_G':b0,'beta_c':b1})
                    else:
                        u = e[0]
                        Ws = switch_at(G, W, u)
                        Gc, Wc = fuzz.contract_edge_signed(G, Ws, e)
                        b0 = fuzz.beta(G, W); b1 = fuzz.beta(Gc, Wc)
                        results_A6r['tested'] += 1
                        if b1 <= b0:
                            results_A6r['passed'] += 1
                        elif len(results_A6r['ces']) < 4:
                            results_A6r['ces'].append({'n':n,'edges':[list(x) for x in edges],'W':[list(x) for x in W],'e':list(e),'switched_at':u,'beta_G':b0,'beta_c':b1})

    # n=6 random sample
    for _ in range(n6_sample):
        G = fuzz.random_connected_graph(6)
        edges = fuzz.edge_list(G)
        m = len(edges)
        if m == 0: continue
        W = {edges[i] for i in range(m) if RNG.random() < 0.5}
        ne = [e for e in edges if not is_bridge(G,e)]
        if not ne: continue
        e = RNG.choice(ne)
        if e not in W:
            Gc,Wc = fuzz.contract_edge_signed(G,W,e)
            b0 = fuzz.beta(G,W); b1 = fuzz.beta(Gc,Wc)
            results_A5r['tested'] += 1
            if b1 <= b0: results_A5r['passed'] += 1
            elif len(results_A5r['ces'])<6:
                results_A5r['ces'].append({'n':6,'edges':[list(x) for x in edges],'W':[list(x) for x in W],'e':list(e),'beta_G':b0,'beta_c':b1})
        else:
            u = e[0]; Ws = switch_at(G,W,u)
            Gc,Wc = fuzz.contract_edge_signed(G,Ws,e)
            b0 = fuzz.beta(G,W); b1 = fuzz.beta(Gc,Wc)
            results_A6r['tested'] += 1
            if b1 <= b0: results_A6r['passed'] += 1
            elif len(results_A6r['ces'])<6:
                results_A6r['ces'].append({'n':6,'edges':[list(x) for x in edges],'W':[list(x) for x in W],'e':list(e),'switched_at':u,'beta_G':b0,'beta_c':b1})

    print(f"A5''  tau={results_A5r['passed']/max(1,results_A5r['tested']):.6f}  ({results_A5r['passed']}/{results_A5r['tested']})  CEs stored: {len(results_A5r['ces'])}")
    for c in results_A5r['ces']: print('  CE:',c)
    print(f"A6''  tau={results_A6r['passed']/max(1,results_A6r['tested']):.6f}  ({results_A6r['passed']}/{results_A6r['tested']})  CEs stored: {len(results_A6r['ces'])}")
    for c in results_A6r['ces']: print('  CE:',c)

if __name__ == '__main__':
    probe()
