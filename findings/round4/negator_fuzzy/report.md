# NEGATOR-FUZZY round 4 report

Envelope: all non-iso graphs on `n ∈ {3,4,5}` × every wrap subset (≈3453 configs); `n=6` with up to 40 wrap samples for C9/C14; 200 samples × edge-count for C15 on `K_5`, `C_6`, `C_6+chord`.

## Results ranked by τ (4 s.f.)

| #  | claim | τ | verdict |
|----|-------|------|---------|
| C3  | `λ_min(L_möb)=0` always | **1.0000** | TRUE |
| C4  | `sorted spec(L_möb) == sorted(spec L_s ∪ spec L_sig)` | **1.0000** | TRUE |
| C6  | single-vertex switching preserves β | **1.0000** | TRUE |
| C7  | every component has `#fiber ∈ {1,2}` | **1.0000** | TRUE |
| C8  | `det(L_s+αI)·det(L_sig+αI)=det(L_möb+αI)` | **1.0000** | TRUE |
| C9  | `dim ker L_sig ≤ dim ker L_s` | **1.0000** | TRUE |
| C10 | `dim ker L_möb = dim ker L_möb²` | **1.0000** | TRUE |
| C12 | `W=∅ ⇒ spec(L_möb)=spec(L_s) doubled` | **1.0000** | TRUE |
| C13 | cocycle switching on `K_4` preserves β | **1.0000** | TRUE |
| C14 | `ker L_s + ker L_sig = ker L_möb` | **1.0000** | TRUE |
| C1  | `β(G) ≥ β(G−e)` for non-wrap edge | 0.8906 | MOSTLY TRUE |
| C5  | `β(G,W)=β(G,E\W)` | 0.8123 | MOSTLY TRUE |
| C15 | `P[β≥1]` non-increasing in `|W|` (sampled) | 0.6087 | MOSTLY TRUE |
| C11 | single-edge wrap flip preserves `spec(L_möb)` | 0.1130 | COUNTEREXAMPLE-RICH |
| C2  | `β(G) ≤ β(G+non-wrap edge between comps)` | 0.0000 | COUNTEREXAMPLE-RICH |

## Minimal counterexamples

- **C1.** `G=({0,1}, other)` on 3 vertices, `W=∅`, remove `(0,1)`: `β=2 → 3` (isolated vertex split). Inequality backwards for cut-edge.
- **C2.** 3 isolated vertices, add non-wrap `(0,1)`: `β=3 → 2`. Merging balanced components via non-wrap always drops β by 1.
- **C5.** `G=K_3`, `W=∅`: β=1. Flip to `W=E`: triangle has odd-wrap cycle, β=0. Parity-sensitive.
- **C11.** `G=K_3`, `W=∅`, flip `(0,1)`: eigenvalue changes `10⁻¹⁷` → `~1`. Generic.
- **C15.** `K_5`: `p_3 ≈ 0`, `p_4 ≈ 0.03` — sampled estimate is ragged; count-monotonicity fails but Bernoulli-probability monotonicity would hold.

## Classification

**Safe to formalize in Lean (τ=1.0000):** C3, C4, C6, C7, C8, C9, C10, C12, C13, C14. C14 essentially restates `s1_cover_ker_dim`; C9 sharpens round 3's weaker `≥ ks−|W|` bound into unconditional `≤` — this is `signed_kernel_le_scalar_kernel` in `L9_Bounds.lean`.

**Not safe to formalize as stated:** C1 (needs non-bridge), C2 (direction inverted — the honest lemma is `β(G+e) ∈ {β(G)−1, β(G)}` for cross-component additions), C5 (parity-sensitive), C11 (genuinely false; useful as "wrap is spectrally detectable").

**Interesting band (τ ∈ [0.3, 0.9]):** C1 (0.8906), C5 (0.8123), C15 (0.6087).
- C1 → add "e is not a bridge" and claim likely closes to τ=1.
- C5 → restrict to Z/2 coboundary class representatives.
- C15 → replace count-monotonicity with Bernoulli-probability monotonicity.
