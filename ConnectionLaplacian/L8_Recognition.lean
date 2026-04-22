/-
ConnectionLaplacian/L8_Recognition.lean

**Stratum L8 — Recognition theorems.**

Assembly layer: the headline results. Each theorem here is the
"mutual recognition" between the spectral (L4, L7), cover (L5), and
cohomological (L6) strata: `finrank ker = #balancedComponents` is
linear algebra = topology = combinatorics, all for the same object.

Three recognition statements:

1. `signedLaplacian_kernel_dim_general` — the corrected version of the
   old `signedLaplacian_kernel_dim` (which was false on arbitrary wrap).
   RHS is `numBalancedComponents` (L6), not `numComponents − numOddWrapComponents`.

2. `connectionLaplacian_kernel_dim_general` — the full connection
   Laplacian kernel dim: `numComponents + numBalancedComponents` for
   Möbius mode, `2 · numComponents` for flat. Reassembles (1) with
   `scalarLaplacian_kernel_dim` via `laplacian_decomposes` (L4).

3. `mobius_kernel_strict_iff_general` — strict inequality between
   flat and Möbius kernel iff at least one component is unbalanced.

The cycle-graph specializations (recovering the original pre-registered
formulas) live here too, as corollaries of (1)–(3) using the L6 cycle
bridge lemma.
-/

import ConnectionLaplacian.L5_Cover
import ConnectionLaplacian.L6_Cohomology
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional

namespace ConnectionLaplacian

open Matrix BigOperators FiniteDimensional

namespace ConnGraph

variable (G : ConnGraph)

/-! ### L8.1 — Signed kernel dim as balanced component count -/

/-- **Theorem (corrected signed Laplacian kernel dim).** The kernel
dimension of the signed Möbius Laplacian equals the number of balanced
connected components of `G`. Proof: apply Mathlib's
`card_ConnectedComponent_eq_rank_ker_lapMatrix` to the orientation
double cover `G̃`, giving `ker(scalarLap G̃) = numComponents G̃`; by
L5.scalarLap_cover_splits the kernel also equals
`ker(scalarLap G) + ker(signedLap G)`; combining with L6.numComponents_cover
and L4.scalarLaplacian_kernel_dim yields the result. -/
theorem signedLaplacian_kernel_dim_general :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' G.signedLaplacianMobius)) =
      G.numBalancedComponents := by
  -- Mathlib: ker(scalarLap G̃) has dim = #π₀(G̃)
  have h1 :
      FiniteDimensional.finrank ℝ
          (LinearMap.ker (toLin' G.orientationDoubleCover.scalarLaplacian)) =
        G.orientationDoubleCover.numComponents :=
    G.orientationDoubleCover.scalarLaplacian_kernel_dim
  -- L6 bridge: #π₀(G̃) = #π₀(G) + #balanced(G)
  rw [G.numComponents_cover] at h1
  -- L5 kernel-dim corollary: ker(scalarLap G̃) dim = ker(scalarLap G) + ker(signedLap G)
  have h2 := G.scalarLap_cover_kernel_dim
  -- L4: ker(scalarLap G) dim = #π₀(G)
  have h3 := G.scalarLaplacian_kernel_dim
  -- Combine.
  omega

/-! ### L8.2 — Connection Laplacian kernel dim (both modes) -/

/-- **Kernel-dim corollary of `laplacian_decomposes` (L4).**

Since `laplacian mobius` is similar (via an invertible `P` and reindex
`prodFinTwoEquivSum`) to `fromBlocks(scalarLap, 0, 0, B)` where
`B = signedLapMobius` on Möbius and `B = scalarLap` on flat, its kernel
dim splits as the sum of the kernel dims of the two diagonal blocks.

Strictly weaker than `laplacian_decomposes` — skips the explicit `P`
and retains only the kernel-dim consequence. Proof strategy: combine
similarity-invariance of kernel dim (via `toLin'_conj` or direct
linear-equiv from `P`), `Matrix.reindex` kernel-dim preservation (via
`Matrix.rank_reindex` + rank-nullity), and the block-diagonal kernel
decomposition `ker(fromBlocks A 0 0 B) ≃ ker A × ker B`. -/
theorem laplacian_kernel_dim_decomposes (mobius : Bool) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian mobius))) =
      FiniteDimensional.finrank ℝ (LinearMap.ker (toLin' G.scalarLaplacian)) +
      FiniteDimensional.finrank ℝ
          (LinearMap.ker (toLin'
              (if mobius then G.signedLaplacianMobius else G.scalarLaplacian))) := by
  obtain ⟨P, hPdet, hreindex⟩ := G.laplacian_decomposes mobius
  have hsim :
      finrank ℝ (LinearMap.ker (Matrix.toLin' (P * G.laplacian mobius * P⁻¹))) =
      finrank ℝ (LinearMap.ker (Matrix.toLin' (G.laplacian mobius))) :=
    finrank_ker_toLin'_conj P (G.laplacian mobius) hPdet
  have hreidx :
      finrank ℝ (LinearMap.ker (Matrix.toLin'
        (Matrix.reindex G.prodFinTwoEquivSum G.prodFinTwoEquivSum
          (P * G.laplacian mobius * P⁻¹)))) =
      finrank ℝ (LinearMap.ker (Matrix.toLin' (P * G.laplacian mobius * P⁻¹))) :=
    finrank_ker_toLin'_reindex G.prodFinTwoEquivSum _
  rw [hreindex] at hreidx
  have hsplit :=
    finrank_ker_toLin'_fromBlocks_diag (K := ℝ)
      G.scalarLaplacian
      (if mobius then G.signedLaplacianMobius else G.scalarLaplacian)
  linarith [hsim, hreidx, hsplit]

/-- **Theorem (general connection Laplacian kernel dim).** The full
Z/2 connection Laplacian's kernel dimension:

  Flat mode: `dim(ker) = 2 · numComponents`.
  Möbius mode: `dim(ker) = numComponents + numBalancedComponents`.

The old formula `2·numComponents − numOddWrapComponents` is recovered
on cycle graphs via the L6 cycle bridge lemma. -/
theorem connectionLaplacian_kernel_dim_general (mobius : Bool) :
    FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian mobius))) =
      (if mobius then G.numComponents + G.numBalancedComponents
                 else 2 * G.numComponents) := by
  rw [G.laplacian_kernel_dim_decomposes mobius]
  rw [G.scalarLaplacian_kernel_dim]
  cases mobius with
  | true =>
    rw [if_pos rfl, if_pos rfl]
    rw [G.signedLaplacian_kernel_dim_general]
  | false =>
    rw [if_neg (by decide : (false : Bool) ≠ true),
        if_neg (by decide : (false : Bool) ≠ true)]
    rw [G.scalarLaplacian_kernel_dim]
    ring

/-! ### L8.3 — Strict inequality (Möbius ker < flat ker iff unbalanced exists) -/

/-- **Theorem (strict inequality).** The Möbius bundle has strictly
smaller kernel than the flat bundle iff at least one component is
unbalanced (has non-trivial wrap class in `H¹`). -/
theorem mobius_kernel_strict_iff_general :
    (FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian true))) <
     FiniteDimensional.finrank ℝ
        (LinearMap.ker (toLin' (G.laplacian false)))) ↔
    G.numBalancedComponents < G.numComponents := by
  have _hle : G.numBalancedComponents ≤ G.numComponents :=
    G.numBalancedComponents_le
  rw [G.connectionLaplacian_kernel_dim_general true,
      G.connectionLaplacian_kernel_dim_general false]
  simp only [if_true, if_false]
  constructor
  · intro h; omega
  · intro h; omega

end ConnGraph

end ConnectionLaplacian
