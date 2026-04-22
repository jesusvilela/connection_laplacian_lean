# AMBIGUATOR Report — Round 3

Paper: `paper/paper.tex` (922 lines)

## 1. Hidden ambiguity in seemingly-precise statements

### 1.1 "Both are real symmetric positive semidefinite" (line 252)
PSD scope unclear (R vs C vs Loewner). §6 silently moves to C^n. PSD is asserted but never proved in paper or linked to Lean.
Fix: "Both are real symmetric and positive semidefinite as quadratic forms on R^V (equivalently, Hermitian PSD on C^V); the Fourier argument in §6 is purely computational."

### 1.2 "Balanced" used with two different scopes
Component-local (Def 4.1, Thm 5.5) vs graph-global (cohomology paragraph at lines 504-511). Only per-component is used in theorems; global appears once then vanishes. Fix: add clarifying remark.

### 1.3 "Wrap holonomy around every cycle trivial" (line 169)
"Every cycle" ambiguous (simple subgraph / closed walk / homology class).
Fix: "...the wrap holonomy, viewed as [σ_W|_C] in H^1(C;Z/2), vanishes; equivalently, every closed walk in C has even wrap count."

### 1.4 Isolated vertex is vacuously balanced — never noted
Def 4.1 vacuously true on singleton components. Correct and necessary (isolated vertex contributes +1 to kernel), but should be explicitly convention-flagged.

### 1.5 Rhat "diagonalises" σ_x (lines 222-223)
R·A·R = 2D not D. Works via R^{-1} = (1/2)R, but factor-of-2 bookkeeping returns at line 311.
Fix: state R^{-1} = (1/2)R up front; show both normalized and unnormalized forms.

## 2. Weakenable / strengthenable / invertible definitions

### 2.1 Def 4.1: weaken ε : V → Bool to ε : C → Bool
Logically equivalent; simplifies Lemma 4.3.

### 2.2 Strengthen to graph-global balance
Would break §1.2 equivalence; doesn't affect theorems.

### 2.3 Invert Thm 4.2 (fibre-card) to "2 ↔ unbalanced, 1 ↔ balanced"
**Would break Cor 4.4.** Sanity: C_4 with W=∅ has 1 balanced component; cover is two C_4's; #π_0(G~) = 2 = 1+1, not 2·1 − 1.

## 3. Unstated assumptions

- §1 exposition tacitly assumes connected G (lines 166-172).
- §6 jumps to C^n without flagging (line 744).
- Thm 4.2 assumes C non-empty (line 538 picks v_0 ∈ C). Fine by Mathlib but unstated.
- Edge orientation: unoriented, Φ symmetric. Worth one line.

## 4. Prose vs. Lean mismatches

### 4.1 Abstract item (iii) weaker than Lean
Prose: "C balanced iff fibre = 2" (one direction only). Lean: both cases. Advertise the dichotomy.

### 4.2 Thm 3.1 existential vs Lean constructive
Prose says "there exists P"; Lean builds P = I_V ⊗_K Rhat explicitly.

### 4.3 Remark on (*) (line 728) cites Python brute-force for K_4
General Lean theorem certifies β(K_4) = 0 symbolically; cite that.

## 5. Notation collisions

- **π_0 / \comp overloaded**: set-of-components AND equivalence-class subscript. Use [u]_~G for the latter.
- **σ_W** called "1-cocycle" (L353), "1-cochain" (L500), class [σ_W] (L507). State upfront: no 2-cells, so C^1 = Z^1.
- **Two Rhats** (Fin 2 / Bool versions). Agree under bot↔0, top↔1. Footgun if the bijection is flipped.
- **β(G)** for "number of balanced components" lacks the standard Betti-meaning flag.
- **tilde-L** (line 388) defined as L_scalar(G~), not a signed Laplacian of the cover. Cor 3.5 could re-state.

## 6. The "step 3" + footnote concession (§4, lines 601-629)
Yes, partially concedes prose ≠ Lean. Prose uses ε_0 via reachability at sheet ⊥; footnote notes Lean uses deck-Z/2-free-action argument. **Both prove the same theorem.** The hedge "slightly different but equivalent route" signals distance. Fix: replace prose with deck-orbit argument, drop the hedge. Secondary: ε_0's value off C is never constrained in prose — note so explicitly.

## 7. Thm 5.5 (thm:strict) quantifier direction (lines 704-708)
"Some component is not balanced" logically correct, but Lean's `mobius_kernel_strict_iff_general` is likely phrased as negation of universal. Swap to "not every component is balanced". Line 713 proof bookkeeping: β ≤ #π_0 follows from subset, not "from Definition 4.1."

## 8. Factual self-contradiction
- Line 121 (abstract): "2,456 configurations"
- Line 836 (§7): "3456 configurations"
- Line 845 (§7): "3,456 configurations agreed"
**Paper contradicts itself.** Run fuzzer once; reconcile. Erosion of confidence in numerical claim.

## 9. Minor

- "base connected component" (L98): non-standard.
- "flat Laplacian agrees with two copies" (L154): imprecise. Say L_scalar ⊗ I_2.
- "interior" (L348): undefined. Say "non-wrap".
- Fourier Re/Im eigenvectors (L745-746): k=0 and k=n/2 are self-conjugate.

## 10. Priority fix list

1. **NUMERICAL**: 2,456 vs 3,456 (§8)
2. **BALANCE SCOPE**: disambiguate around line 507 (§1.2)
3. **FOOTNOTE HEDGE**: drop or upgrade §4 Step 3 hedge (§6)
4. **PSD CLARIFICATION**: line 252 scope + citation (§1.1)
5. **ISOLATED VERTEX**: convention note (§1.4)
6. **THM 5.5 QUANTIFIER**: direction swap (§7)
7. **π_0 NOTATION**: disambiguate set vs class subscript (§5.1)
8. **Rhat FACTOR 2**: state R^{-1} = (1/2)R once (§1.5)

Rest is prose polish.
