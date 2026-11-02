# The connection Laplacian enters Mathlib: a mathematical field guide

> **Purpose.** Explain, in ordinary mathematical language, how the existing
> Z/2 connection-Laplacian development can be factored into reusable Mathlib
> results. This guide is an orientation aid, **not** a proof certificate for
> the port. The canonical source formalization remains this repository.

**Work in progress:** [verified development branch](https://github.com/jesusvilela/mathlib4/tree/feat/signed-graph-laplacian) and [clean submission branch](https://github.com/jesusvilela/mathlib4/tree/submission/signed-graph-laplacian). The submission branch excludes the fork-only CI workflow; an upstream PR has **not** yet been opened.
**Upstream-based, single-commit patch:** [`81a0413`](https://github.com/jesusvilela/mathlib4/commit/81a0413db77f574663207b64541350d493dcd2ce), containing only the signed-Laplacian module and its `Mathlib.lean` import. The separate [upstream-base verification run](https://github.com/jesusvilela/mathlib4/actions/runs/41434003371) **passed** against synchronized Mathlib `master`, including build, `mk_all` check, targeted `leanchecker`, declaration linter and `#print axioms` checks. The clean submission branch and verification branch contain identical source blobs for the two proposed Mathlib files; only the latter has a temporary workflow.
**First proposed library module:**
[`SignedLapMatrix.lean`](https://github.com/jesusvilela/mathlib4/blob/feat/signed-graph-laplacian/Mathlib/Combinatorics/SimpleGraph/SignedLapMatrix.lean).

## Why the mathematical object belongs in a general library

A simple graph tells us *which* vertices can interact; an edge label tells us
*how values are transported*. The first Mathlib contribution uses existing
`SimpleGraph.EdgeLabeling` rather than importing the paper's entire
`ConnGraph` structure.

For a finite undirected graph `G=(V,E)`, give each edge a symmetric sign
`σ_uv ∈ {+1,-1}` (positive for ordinary edges, negative for *wrap* edges).
Define the signed adjacency and signed Laplacian:

```text
Aσ(u,v) = σ_uv  when {u,v} is an edge; otherwise 0
Lσ       = D - Aσ
```

Here `D` is the degree matrix. These definitions expose the operator
independently of the paper's double-cover and block-matrix constructions.

- All edges positive: `Lσ = L`, the usual graph Laplacian.
- All edges negative: `Lσ = D + A`, the **signless Laplacian**.
- Mixed signs: the same symmetric operator handles genuine Z/2 transport.

## The three transitions that matter

```mermaid
flowchart LR
  A["Unsigned graph + signed edge labels"] --> B["Signed Laplacian D - Aσ"]
  B --> C["Sum-of-squares energy"]
  C --> D["Positive semidefiniteness"]
  D --> E["Zero modes = parallel sections"]
  E --> F["Balance / cycle holonomy"]
  F --> G["Kernel dimension = number of balanced components"]
  G --> H["Double-cover / 2-layer connection Laplacian"]
```

### 1. Energy: positivity is geometric, not numerical luck

For every real vector `x : V → ℝ`,

```text
xᵀ Lσ x = ½ Σ_u Σ_v [u~v] (x_u - σ_uv x_v)².
```

The double sum visits each undirected edge twice. Therefore each contribution
is a square and the operator is positive semidefinite.

An ordinary edge contributes `(x_u - x_v)²`; a wrap edge contributes
`(x_u + x_v)²`. The sign changes what it means for a vector to remain
locally constant, *not* the nonnegativity of its energy.

The source proof is in `ConnectionLaplacian/L13_PSD.lean`. The new Mathlib
proof compiled at commit [`c13c8a5`](https://github.com/jesusvilela/mathlib4/commit/c13c8a5c4107ecf0334f02e94705a44201171273).
Its cleaned successor [`45f9e71`](https://github.com/jesusvilela/mathlib4/commit/45f9e71b2f74ffb4e12240192d6c34df965ed2b4)
subsequently [passed the current Mathlib build, generated-import check,
and targeted Lean proof-term checker](https://github.com/jesusvilela/mathlib4/actions/runs/41432293826),
without source warnings. An explicit `#print axioms` audit of four central
results found only `propext`, `Classical.choice`, and `Quot.sound`.

### 2. Null vectors are parallel sections

Since every summand is nonnegative, zero energy is equivalent to

```text
x_u = σ_uv x_v     on every edge {u,v}.
```

Combined with positive semidefiniteness, this is also the characterization
of the *operator* kernel `Lσ x = 0`. This is the local-to-global bridge:
along each connected path, values propagate with the product of edge signs.

On a closed walk, transport returns to the original vertex. A negative sign
product would require `x_u = -x_u`, hence `x_u = 0` over the reals.
Connectedness then propagates zero to the entire component.

### 3. Balance and dimension

A component is **balanced** if one can choose a vertex sign
`τ : V → {+1,-1}` so that

```text
σ_uv = τ_u τ_v       for every edge in the component.
```

Equivalently, the product of edge signs around **every closed walk** is +1;
equivalently, the wrap indicator is a Z/2 coboundary. This is the precise
meaning behind the cohomological formulation in `L6_Cohomology.lean`
and `L12_WalkH1.lean`.

On a balanced component, all parallel sections are of the form
`x_v = c τ_v`, so they form a one-dimensional real vector space. On an
unbalanced component, the only parallel section is zero. Consequently:

```text
dimℝ ker Lσ = number of balanced connected components of G.
```

This is the mathematical target of `L8_Recognition.lean` and of the
eventual second Mathlib contribution.

A useful related *gauge* viewpoint: for globally balanced `G`, the diagonal
matrix `T = diag(τ_v)` satisfies `T²=I` and `Lσ=T L T`.
Thus the **whole spectrum**, not only the kernel dimension, agrees with
that of the ordinary Laplacian in the globally balanced case. On disconnected
graphs this applies component by component where a gauge exists.

## The K4 warning: total wrap parity is NOT balance

A single total count of negative edges cannot detect all cycle obstructions.
For example, in `K4`, make only edges `{1,2}` and `{3,4}` negative.
There are **two** negative edges in total (even), but the triangle
`1-2-3-1` contains **one** negative edge (odd). This signing is unbalanced.

The earlier number-of-odd-wrap-components criterion is valid for a
single-cycle graph, where the cycle space has rank one, but not for a
general graph. The corrected invariant is the existence of a vertex gauge
on each component, or equivalently trivial sign holonomy on every cycle.

Never reintroduce the old total-parity criterion when porting to Mathlib.

## What is formally established, and what remains

| Layer | Status | Source or gate |
|---|---|---|
| Original Z/2 development | Repository-reported Lean verification at **v4.11.0** | `ConnectionLaplacian.lean`, `Hardening/`, its CI and evidence map |
| Current Mathlib definitions, symmetry, signless case | **Cleaned development build, Mathlib declaration linter and targeted checker passed at `b8c27d7`** | [Verified CI](https://github.com/jesusvilela/mathlib4/actions/runs/41433770120) |
| General energy, PSD and edgewise-kernel theorems | **Compiled and Mathlib-linted at `b8c27d7`; four main theorems axiom-audited** | [Verified CI](https://github.com/jesusvilela/mathlib4/actions/runs/41433770120) |
| Balance classification in Mathlib | **Future port**, mathematically justified by source | The future gauge/holonomy and componentwise kernel proofs |
| One-commit upstream-based submission patch | **Compiler-, checker-, linter- and axiom-audited; community acceptance pending** | [Upstream-based verification CI](https://github.com/jesusvilela/mathlib4/actions/runs/41434003371) |
| Full two-layer connection Laplacian in Mathlib | **Future integration** | Keep its matrix identification and cover assumptions explicit |

A theorem's mathematical correctness, the fidelity of its Lean statement,
the acceptance of its proof by the current Lean kernel, and its suitability
for Mathlib are **four different checks**.

## Reproducible finite counterexample and energy audit

The dependency-free script
[`scripts/verify_signed_laplacian_small.py`](../scripts/verify_signed_laplacian_small.py)
checks **all** signed simple graphs on labeled vertex sets of size 1 through 4:
each potential unordered edge is absent, positive or negative (760 cases).
It uses exact rational Gaussian elimination rather than floating-point
rank thresholds.

Run:

```bash
python3 scripts/verify_signed_laplacian_small.py
```

The [2026-11-02 GitHub Actions run](https://github.com/jesusvilela/connection_laplacian_lean/actions/runs/41429453701)
passed the exact audit after adding orientation-cover tests. Its checks include:

- All **760** signed simple graphs on one through four labeled vertices.
- **59,808** vector energy identities using `{-1,0,1}` entries.
- **420** balanced whole-graph signings with a checked diagonal-gauge conjugation.
- For every signed graph, the ordinary double cover satisfies
  `components(cover) = components(base) + balancedComponents(base)`.
- For every signed graph, exact rational rank confirms
  `nullity(coverLap) = nullity(baseLap) + nullity(signedLap)`.
- For `K4`, exactly **8** of 64 signings are balanced, while **28** of
  the even-negative-edge signings are unbalanced.

The script explicitly constructs the two-sheet cover and computes its
connected components **independently** of matrix rank. These are bounded
regression checks (**measured evidence**), not universally quantified
Lean proofs.

## Review workflow

1. Compile the proposed module using the fork's `lean-toolchain`:
   `lake exe cache get` and
   `lake build Mathlib.Combinatorics.SimpleGraph.SignedLapMatrix`.
2. Check that the actual theorem statements reflect the mathematical
   definitions; resolve every compiler error without `sorry` or new axioms.
3. Run the relevant Mathlib linters, `lake exe mk_all --check`, and an
   explicit axiom audit where supported.
4. Keep the first upstream PR restricted to a maintainable foundation.
   The temporary `.github/workflows/signed-lap-ci.yml` belongs to the
   author's fork **only** and must not be included in the upstream patch.
5. Disclose AI assistance honestly and have the contributor personally
   review and explain the mathematics, definitions and Lean proofs.
   GitHub/Zulip discussions should be written by the contributor, in
   accordance with Mathlib's current policy.

## Human reconstruction before approaching reviewers

The code compiling is necessary but not sufficient for a useful Mathlib PR.
The contributor should be able to answer the following without outsourcing
the explanation to an AI assistant:

1. **Model:** Why does an unoriented `SimpleGraph.EdgeLabeling Bool` supply
   one consistent sign per edge? Why do negative labels encode a
   `ℤ/2ℤ`-connection rather than arbitrary unitary transport?
2. **Energy:** Starting from `Lσ = D - Aσ`, derive
   `xᵀLσx = (1/2) Σ_{u~v} (x_u - σ_uv x_v)²`.
   Explain the factor of one-half and the difference between ordered
   vertex pairs and unordered edges.
3. **Kernel:** Explain why vanishing of the sum of nonnegative squares is
   equivalent to the edgewise relation `x_u = σ_uv x_v`, and why the
   positive-semidefinite kernel theorem lets us replace zero *energy*
   with zero *operator action*.
4. **Topology:** On a connected component, explain how sign propagation
   around a closed walk detects nontrivial holonomy. Give a small
   example showing that an *even total number* of negative edges is
   not sufficient for balance.
5. **Library design:** Why is this first PR limited to reusable matrix
   definitions, positivity and kernel characterization, leaving the
   full double cover and balanced-component dimension theorem for
   follow-up contributions? What generalizations might Mathlib
   reviewers reasonably ask for?

This is a **self-study checklist**, not a comment or PR description to
paste into GitHub or Zulip. Mathlib's
[AI contribution policy](https://leanprover-community.github.io/contribute/index.html#use-of-ai)
requires substantial understanding and human-written GitHub/Zulip discussion.
The precise extent of AI assistance must also be disclosed when a PR is
eventually opened.

The objective is not to transfer the entire research archive at once.
It is to expose the smallest stable operators and invariants that other
mathematicians can reuse, inspect and independently reconstruct.
