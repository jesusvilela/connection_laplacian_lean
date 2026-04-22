"""Additional stress: random graphs on 6-8 vertices with multiple components."""
import random
import itertools
from check_fiber import fiber_counts, test_graph

random.seed(2026)

all_ce = []
total = 0
for trial in range(200):
    n = random.randint(4, 8)
    V = list(range(n))
    possible_edges = [(i, j) for i in range(n) for j in range(i+1, n)]
    # p in [0.2, 0.6]
    p = random.uniform(0.15, 0.6)
    E = [e for e in possible_edges if random.random() < p]
    if not E:
        continue
    # Enumerate all wrap subsets if |E| <= 10, else sample 200
    if len(E) <= 10:
        wrap_iter = []
        for r in range(len(E) + 1):
            for s in itertools.combinations([frozenset(e) for e in E], r):
                wrap_iter.append(frozenset(s))
    else:
        Efs = [frozenset(e) for e in E]
        wrap_iter = []
        for _ in range(400):
            mask = random.getrandbits(len(Efs))
            w = frozenset(Efs[i] for i in range(len(Efs)) if (mask >> i) & 1)
            wrap_iter.append(w)
    tested, ces = test_graph(f"rand{trial}_n{n}_e{len(E)}", V, E, wrap_subsets=wrap_iter)
    total += tested
    if ces:
        all_ce.extend(ces)
        print(f"TRIAL {trial} n={n} E={E}: {len(ces)} counterexamples")
        print(ces[0])

print(f"Total random configs: {total}, counterexamples: {len(all_ce)}")
