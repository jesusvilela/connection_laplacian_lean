# Critic Report — `laplacian_kernel_dim_decomposes` and meta-audit

Target: `ConnectionLaplacian/L8_Recognition.lean:85-92` (currently `sorry`).
Meta-audit: `L8_Recognition.lean:51-68` (`signedLaplacian_kernel_dim_general`, claimed closed).

## Findings

1. **(WHAT) Statement is well-typed, but the reindex-invariance obligation is non-trivial.**
   (WHERE) `L8_Recognition.lean:85-92`; `KernelDimension.lean:102-104,229-238`.
   (SEVERITY) Low/informational. `G.laplacian mobius : Matrix (V × Fin 2) (V × Fin 2) ℝ` while `fromBlocks _ _ _ _ : Matrix (V ⊕ V) (V ⊕ V) ℝ`. The bridge `prodFinTwoEquivSum` is used only inside `laplacian_decomposes`. `finrank (ker (toLin' M)) = finrank (ker (toLin' (reindex e e M)))` is provable: `Matrix.toLin'_reindex` (ToLin.lean:372) rewrites `toLin' (reindex e₁ e₂ M) = (funCongrLeft ..) ∘ₗ toLin' M ∘ₗ (funCongrLeft ..)` — both outer maps are `LinearEquiv`s, so `ker` is `LinearEquiv.map`-transferred and `finrank` is preserved. No invariance lemma is imported yet; the proof must build it. No crack, but a real obligation.

2. **(WHAT) `mobius=false` branch: RHS `2·dim ker scalarLap` is correct but not "obviously `I⊗scalarLap`".**
   (WHERE) `KernelDimension.lean:115-136` (`laplacian_flat_entry`).
   (SEVERITY) None substantively. The flat block is `[[scalarLap uv, 0],[0, scalarLap uv]]`, i.e. fiber-diagonal, literally `scalarLap ⊗ I₂` (not `I ⊗ scalarLap`). As a linear map on `V×Fin2 → ℝ`, `ker ≅ ker scalarLap × ker scalarLap`, so `dim = 2·dim ker scalarLap`. ✓ But note: the charter's hint "I ⊗ scalarLap" flips the Kronecker order — this is a cosmetic difference. For a general `A`, `dim ker (A ⊗ I_k) = k·dim ker A` IS a general fact (Kronecker kernel = tensor of kernels), so this is fine.

3. **(WHAT) `mobius=true` similarity: invertibility via `det ≠ 0` IS enough in Mathlib but conversion is non-trivial.**
   (WHERE) `KernelDimension.lean:230-232` (`P.det ≠ 0`); target uses it transitively.
   (SEVERITY) Low. `Matrix.det_ne_zero_iff_isUnit` (or equivalent) exists. Over a commutative ring, `det ≠ 0 ↔ IsUnit` holds only over a field/integral domain via `Matrix.isUnit_iff_isUnit_det`; ℝ is a field, so `IsUnit P` follows. Then `ker(P*M*P⁻¹) ≃ ker M` as linear maps via composing with `toLin'(P)` / `toLin'(P⁻¹)` equivalences. **Real crack:** `laplacian_decomposes` returns `P.det ≠ 0`, not `IsUnit P` or a `LinearEquiv`. The proof of `laplacian_kernel_dim_decomposes` must rebuild invertibility — multi-step. Mathlib lemma to lean on: `Matrix.toLin'_mul` + `LinearEquiv` from an invertible matrix.

4. **(WHAT) `toLin'` scalar ring is correct, no coercion crack.**
   (WHERE) `KernelDimension.lean:361` and Mathlib `ToLin.lean:306`.
   (SEVERITY) None. `toLin' : Matrix m n R ≃ₗ[R] (n→R) →ₗ[R] (m→R)` with R=ℝ; `LinearMap.ker` of a linear map over ℝ is well-typed. Fine.

5. **(CRITICAL CRACK) Meta-audit: `signedLaplacian_kernel_dim_general` is NOT legitimately closed.**
   (WHERE) `L8_Recognition.lean:51-68` uses `G.scalarLap_cover_kernel_dim` (line 64), which is defined at `L5_Cover.lean:198-204` with body `:= by sorry`.
   (SEVERITY) HIGH. The target theorem in L8.1 compiles but depends on a sorry. `CONTEXT.md` line 15 explicitly lists `scalarLap_cover_kernel_dim` as one of the four open sorries. The charter's framing ("claimed closed") is accurate only in the sense that the `theorem ... by` body has no `sorry` token — but the transitive dependency is open. Cross-check with `L6.componentProj_fiber_card` (also `sorry` at L6_Cohomology.lean:108) — `numComponents_cover` (used at L8_Recognition.lean:62) depends on it. Thus TWO theorems called from `signedLaplacian_kernel_dim_general` are sorry-dependent.

6. **(WHAT) `omega` at `L8_Recognition.lean:68` is legitimate.**
   (WHERE) same.
   (SEVERITY) None. After `rw [numComponents_cover] at h1` we have `h1 : X = G.numComponents + G.numBalancedComponents`, `h2 : X = A + B`, `h3 : A = G.numComponents`, goal `B = G.numBalancedComponents` where X,A,B are opaque ℕ. Pure linear ℕ arithmetic; `omega` handles it. No non-negativity assumption is smuggled (finrank over ℕ is already non-negative by type).

7. **(WHAT) `scalarLaplacian_kernel_dim` definition match is tight.**
   (WHERE) `KernelDimension.lean:66-67, 360-364`.
   (SEVERITY) None. `G.scalarLaplacian := G.graph.lapMatrix ℝ` is a `def`, so `unfold` reduces exactly to Mathlib's `lapMatrix ℝ`, and `numComponents := Fintype.card G.graph.ConnectedComponent` aligns with Mathlib's `card_ConnectedComponent_eq_rank_ker_lapMatrix`. Clean.

## Counterexample statement

No counterexample exists under scope `{mobius ∈ Bool, G : ConnGraph finite}`: the decomposition is mathematically correct — kernel of `fromBlocks A 0 0 B` really is `ker A ⊕ ker B`, and similarity/reindex preserve finrank over ℝ. The target theorem is TRUE. The `sorry` is a proof-engineering gap, not a logical flaw.

However, **the meta-audit produces a dependency-level counterexample to the claim "signedLaplacian_kernel_dim_general is closed":** transitive proof uses `scalarLap_cover_kernel_dim` (sorry) and `numComponents_cover` (which uses `componentProj_fiber_card`, sorry). Both sorries are listed in `findings/CONTEXT.md` as open but the L8 theorem is presented as closed — this is a bookkeeping crack, severity HIGH for pre-registration discipline.
