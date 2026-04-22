/-
ConnectionLaplacian/L6_Cohomology.lean

**Stratum L6 — Z/2 Cohomology of the connection.**

The wrap predicate `wrap : edgeSet → Prop` is a 1-cocycle with
coefficients in Z/2: `σ : edgeSet → ZMod 2, σ(e) = 1 if wrap e else 0`.
Its class `[σ] ∈ H¹(G; Z/2)` is the topological obstruction to
orientability of the Z/2 line bundle defined by `wrap`.

For a connected component `C`, `[σ|_C] = 0 ∈ H¹(C; Z/2)` iff there
exists a vertex 2-coloring `ε : V(C) → Bool` with
`wrap e ↔ ε(u) ≠ ε(v)` for every edge `e = {u, v}` in `C`. Such a
component is called **balanced** (Zaslavsky / Harary-Kabell). A
component is balanced iff its orientation double cover preimage has
two disconnected sheets (equivalently: the deck action restricted to
that component fixes each sheet as a set).

The signed-Laplacian kernel dimension is `numBalancedComponents`
(proved in L8 using the L5 cover split + Mathlib scalar kernel dim).

For the pre-registered scope (n-cycle): `H¹(C_n; Z/2) = ZMod 2`, and
the class is detected by `(total wrap count in C_n) mod 2`. This is
why the original `numOddWrapComponents` formula is correct on cycles
but false in general (non-cycle connected components have
`H¹ = (ZMod 2)^(|E| − |V| + 1)` with multiple independent classes).
-/

import ConnectionLaplacian.KernelDimension
import ConnectionLaplacian.L5_Cover

namespace ConnectionLaplacian

open Matrix BigOperators

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L6.1 — The wrap cocycle -/

/-- The wrap predicate reified as a Z/2-valued 1-cochain on edges. -/
noncomputable def wrapCocycle : G.graph.edgeSet → ZMod 2 :=
  fun e => if G.wrap e then 1 else 0

/-! ### L6.2 — Balanced components via vertex 2-coloring -/

/-- A connected component `C` is **balanced** iff there is a vertex
2-coloring `ε : G.V → Bool` such that on every edge of the component,
the coloring changes sign exactly on wrap edges. Equivalently: the
restriction of the wrap cocycle to `C` is a coboundary. -/
def isBalanced (C : G.graph.ConnectedComponent) : Prop :=
  ∃ ε : G.V → Bool, ∀ (u v : G.V), ∀ (h : G.graph.Adj u v),
    G.graph.connectedComponentMk u = C →
    (G.wrap ⟨s(u, v), (SimpleGraph.mem_edgeSet G.graph).mpr h⟩ ↔ ε u ≠ ε v)

noncomputable instance decIsBalanced (C : G.graph.ConnectedComponent) :
    Decidable (G.isBalanced C) := Classical.dec _

/-- Number of balanced components. Corrected replacement for
`numComponents − numOddWrapComponents` — agrees with the latter on
cycle graphs but not in general. -/
noncomputable def numBalancedComponents : ℕ :=
  Fintype.card { C : G.graph.ConnectedComponent // G.isBalanced C }

/-! ### L6.3 — Bound: balanced count ≤ total component count -/

lemma numBalancedComponents_le :
    G.numBalancedComponents ≤ G.numComponents := by
  unfold numBalancedComponents numComponents
  exact Fintype.card_subtype_le _

/-! ### L6.4 — Cover-count formula (bridge to L5) -/

/-- The sheet-forgetting projection `(v, b) ↦ v`, a graph homomorphism
from the orientation double cover to the base graph. An edge in the cover
`(u, b) — (v, c)` requires `G.graph.Adj u v` (the wrap-status of the edge
only constrains `b` vs `c`), so `Prod.fst` preserves adjacency. -/
def coverProj : G.coverGraph →g G.graph where
  toFun := Prod.fst
  map_rel' := by
    rintro ⟨u, b⟩ ⟨v, c⟩ h
    -- `h : G.coverGraph.Adj (u,b) (v,c)` unfolds to `G.coverAdj (u,b) (v,c)`.
    -- The `dif_pos hadj` branch of `coverAdj` requires `G.graph.Adj u v`.
    change G.coverAdj (u, b) (v, c) at h
    unfold coverAdj at h
    by_cases hadj : G.graph.Adj u v
    · exact hadj
    · rw [dif_neg hadj] at h; exact h.elim

/-- The induced projection π₀(G̃) → π₀(G) on connected components. -/
noncomputable def componentProj :
    G.coverGraph.ConnectedComponent → G.graph.ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map G.coverProj

/-- **Fiber-cardinality lemma.** The number of connected components of
`G̃` mapping to a fixed component `C` of `G` is:
- 2 if `C` is balanced (the two sheets stay separated)
- 1 if `C` is unbalanced (the wrap non-trivialities merge the sheets).

Key direction of the proof: use a path-based construction. Pick a vertex
`v ∈ C`. Balanced ↔ (v, false) and (v, true) lie in different G̃-components
↔ the fiber has two elements rather than one. -/
lemma componentProj_fiber_card (C : G.graph.ConnectedComponent) :
    Fintype.card
      { D : G.coverGraph.ConnectedComponent // G.componentProj D = C } =
      (if G.isBalanced C then 2 else 1) := by
  sorry

/-- **Bridge to L5.** The number of connected components of the
orientation double cover equals `numComponents G + numBalancedComponents G`
(each balanced component lifts to 2 components; each unbalanced lifts
to 1). Used by L8 to translate Mathlib's scalar kernel-dim theorem on
`G̃` into the signed kernel-dim formula on `G`.

Proof: partition π₀(G̃) by the base projection; each fiber has size 2
(balanced) or 1 (unbalanced); sum gives `#balanced · 2 + #unbalanced · 1 =
#total + #balanced`. -/
theorem numComponents_cover :
    G.orientationDoubleCover.numComponents =
      G.numComponents + G.numBalancedComponents := by
  show Fintype.card G.orientationDoubleCover.graph.ConnectedComponent = _
  change Fintype.card G.coverGraph.ConnectedComponent = _
  -- Step 1: π₀(G̃) ≃ Σ C : π₀(G), fiber over C, via D ↦ ⟨projD, D, rfl⟩.
  have hsig : Fintype.card G.coverGraph.ConnectedComponent =
      Fintype.card
        (Σ C : G.graph.ConnectedComponent,
            { D : G.coverGraph.ConnectedComponent // G.componentProj D = C }) := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun D => ⟨G.componentProj D, D, rfl⟩
        invFun := fun p => p.2.1
        left_inv := fun _ => rfl
        right_inv := fun ⟨_, _, hDC⟩ => by subst hDC; rfl }
  rw [hsig, Fintype.card_sigma]
  -- Step 2: replace each fiber-card with (if balanced then 2 else 1).
  simp_rw [G.componentProj_fiber_card]
  -- Step 3: combinatorial sum identity.
  unfold numComponents numBalancedComponents
  rw [show (fun C : G.graph.ConnectedComponent =>
              if G.isBalanced C then (2 : ℕ) else 1) =
          (fun C => 1 + if G.isBalanced C then 1 else 0) from
      funext (fun _ => by split_ifs <;> rfl)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one]
  congr 1
  rw [Fintype.card_subtype, ← Finset.sum_boole]
  rfl

/-! ### L6.5 — Cycle-case: balanced iff even total wrap count

**Cycle corollary.** For a cycle graph (where `H¹ = ZMod 2`),
a connected component is balanced iff its total wrap count is even.
This recovers the original `numOddWrapComponents` formulation as the
correct characterization on the pre-registered (cycle) scope, so the
old `signedLaplacian_kernel_dim` statement on cycles is a corollary
of the general statement in L8.

Statement `theorem cycle_isBalanced_iff_even_wrap` TBD once the
cycle-specific `ConnGraph` construction is factored out of
`CycleSpectrum.lean`. -/

end ConnGraph

end ConnectionLaplacian
