"""Generate the Lean convention-anchor battery from the INDEPENDENT
(paper-only) implementation in findings/round8/independent_impl.py.

For each battery instance the generator emits a concrete ConnGraph and
two `example`s asserting that the formalization's scalarLaplacian and
signedLaplacianMobius equal the literal matrices computed by the
independent implementation. Lean must compile the whole file; any
convention drift anywhere fails the build.

Deterministic: fixed graph families, exhaustive wrap subsets for graphs
with <= 3 edges, seeded wrap patterns beyond that.
"""
import itertools
import json
import random
import sys

import numpy as np

sys.path.insert(0, "findings/round8")
from independent_impl import scalar_laplacian, signed_laplacian


def unlabeled_graphs():
    """Hand-listed unlabeled simple graphs (vertex set range(n), adjacency
    lists), covering n=2,3 fully and n=5 disconnected specials; n=4 picks
    five representatives (all unlabeled n=4 graphs are covered by the n=8
    sweep's induced subgraphs anyway)."""
    fams = [
        (2, []),                    # 2 isolated
        (2, [(0, 1)]),              # single edge
        (3, []),                    # 3 isolated
        (3, [(0, 1)]),              # edge + isolated
        (3, [(0, 1), (1, 2)]),      # path P3
        (3, [(0, 1), (0, 2), (1, 2)]),  # triangle
        (4, [(0, 1), (1, 2), (2, 3)]),  # path P4
        (4, [(0, 1), (0, 2), (0, 3)]),  # star K1,3
        (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),  # cycle C4
        (4, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]),  # C4 + diagonal (paw-ish)
        (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),  # K4
        (5, [(0, 1), (0, 2), (1, 2), (3, 4)]),  # K3 + K2 (disconnected)
        (5, [(0, 1), (1, 2), (2, 3), (3, 0)]),  # C4 + isolated
    ]
    return fams


def wrap_patterns(n, edges):
    e = len(edges)
    if e <= 3:
        return list(itertools.chain.from_iterable(
            itertools.combinations(edges, k) for k in range(e + 1)))
    rng = random.Random(20261015)
    pats = [(), tuple(edges), (edges[0],), (edges[-1],)]
    while len(pats) < 8:
        pats.append(tuple(rng.sample(edges, rng.randint(2, e - 1))))
    return pats


def mat_literal(M):
    """Emit an if-chain matrix literal over Fin n (avoids !![] data-literal
    evaluation issues in simp: the if-chain uses the same decidable-ite
    machinery that evaluates the LHS)."""
    M = np.rint(np.asarray(M, dtype=float)).astype(int)
    n = M.shape[0]
    def leaf(u, v):
        return f"({int(M[u, v])} : ℝ)"
    def chain(u, v):
        if v == n - 1:
            return leaf(u, v)
        return f"if v = {v} then {leaf(u, v)} else {chain(u, v + 1)}"
    def outer(u):
        if u == n - 1:
            return chain(u, 0)
        inner = chain(u, 0)
        return f"if u = {u} then {inner} else {outer(u + 1)}"
    return f"(Matrix.of fun (u v : Fin {n}) => {outer(0)} : Matrix (Fin {n}) (Fin {n}) ℝ)"


def esc(s):
    return s


def emit_instance(idx, n, edges, wrap_edges):
    name = f"B{idx}"
    edge_set = "{" + ", ".join(f"({u}, {v})" for u, v in
                               [p for e in edges for p in (e, e[::-1])]) + "}"
    wrap_set = "{" + ", ".join(f"s({u}, {v})" for u, v in wrap_edges) + "}"
    adj = np.zeros((n, n), int)
    for u, v in edges:
        adj[u, v] = adj[v, u] = 1
    W = {frozenset(e) for e in wrap_edges}
    sl = mat_literal(signed_laplacian(adj, W))
    sc = mat_literal(scalar_laplacian(adj))

    gname, ename, aname, wname = f"G_{name}", f"E_{name}", f"A_{name}", f"W_{name}"
    out = []
    out.append(f"def {ename} : Finset (Fin {n} × Fin {n}) := {edge_set}")
    out.append(f"def {aname} (u v : Fin {n}) : Prop := (u, v) ∈ {ename}")
    out.append(f"instance : DecidableRel {aname} := fun _ _ => Finset.decidableMem _ _")
    out.append(f"def {wname} : Finset (Sym2 (Fin {n})) := {wrap_set}")
    out.append(f"def {gname} : ConnGraph where")
    out.append(f"  V := Fin {n}")
    out.append("  graph :=")
    out.append(f"    {{ Adj := {aname}")
    out.append("      symm := by")
    out.append("        intro u v h")
    out.append(f"        simp [{aname}, {ename}, Finset.mem_insert, Finset.mem_singleton,")
    out.append("            Prod.mk.injEq] at h ⊢")
    out.append("        <;> omega")
    out.append("      loopless := by")
    out.append("        intro u")
    out.append(f"        simp [{aname}, {ename}, Finset.mem_insert, Finset.mem_singleton,")
    out.append("            Prod.mk.injEq]")
    out.append("        <;> omega }")
    out.append(f"  decrel := fun _ _ => Finset.decidableMem _ _")
    out.append(f"  wrap := fun e => e.val ∈ {wname}")
    out.append(f"  decwrap := fun _ => Finset.decidableMem _ _")
    out.append("")
    out.append(f"example : (show Matrix (Fin {n}) (Fin {n}) ℝ from {gname}.signedLaplacianMobius) =")
    out.append(f"    {sl} := by")
    out.append("  ext u v")
    out.append("  fin_cases u <;> fin_cases v <;>")
    out.append(f"    simp [signedLaplacianMobius, {gname}, degree, {aname}, {ename}, {wname},")
    out.append("          SimpleGraph.neighborFinset]")
    out.append("  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num")
    out.append("")
    out.append(f"example : (show Matrix (Fin {n}) (Fin {n}) ℝ from {gname}.scalarLaplacian) =")
    out.append(f"    {sc} := by")
    out.append("  ext u v")
    out.append("  fin_cases u <;> fin_cases v <;>")
    out.append(f"    simp [scalarLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,")
    out.append(f"          SimpleGraph.adjMatrix, {gname}, {aname}, {ename}, SimpleGraph.degree,")
    out.append("          SimpleGraph.neighborFinset, Matrix.of_apply, Matrix.cons_val_zero,")
    out.append("          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,")
    out.append("          Matrix.vecHead, Matrix.vecTail, Zero.toOfNat0, Matrix.zero_apply]")
    out.append("  all_goals first | exact card_filter_univ_cast _ _ (by decide) | decide | norm_num")
    out.append("")
    return "\n".join(out)


def main():
    header = '''/-
Convention anchoring BATTERY (generated).

Generated by findings/round8/gen_battery.py; every literal matrix below was
computed by the INDEPENDENT paper-only implementation
(findings/round8/independent_impl.py, written from paper.tex alone).
Lean must verify each equality by evaluating the formalization's own
definitions on the concrete instance. Any convention drift fails this file.

Graph families: all unlabeled graphs on n=2,3 vertices, five representatives
at n=4 (P4, K1,3, C4, C4+diagonal, K4), and two disconnected n=5 specials.
Wrap subsets are exhaustive for graphs with <= 3 edges; beyond that a fixed
seeded selection of 8 patterns (including empty, single-edge and all-wrap).
-/
import ConnectionLaplacian

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

set_option maxHeartbeats 4000000

/-- Bridge lemma: lift a `decide`-provable card over a finite type to R. -/
theorem card_filter_univ_cast {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (k : ℕ)
    (h : (Finset.filter p Finset.univ).card = k) :
    ((Finset.filter p Finset.univ).card : ℝ) = k := by rw [h]

'''
    parts = [header]
    table = []
    idx = 0
    for n, edges in unlabeled_graphs():
        for wp in wrap_patterns(n, edges):
            idx += 1
            table.append({"id": f"B{idx}", "n": n, "edges": edges,
                          "wrap": list(wp)})
            parts.append(emit_instance(idx, n, edges, wp))
    parts.append("end Hardening\n")
    out = "\n".join(parts)
    with open("Hardening/ConventionBattery.lean", "w", encoding="utf-8", newline="\n") as f:
        f.write(out)
    with open("findings/round8/battery_instances.json", "w") as f:
        json.dump(table, f, indent=1)
    print(f"generated {idx} instances ({2*idx} example proofs)")


if __name__ == "__main__":
    main()
