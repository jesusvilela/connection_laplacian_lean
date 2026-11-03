# v.0.0.7 — Hexagon-ready manuscript, scope and provenance

**Publication status:** preparation notes only; the GitHub release must not be created until `paper/paper.pdf` has been regenerated, checked against `paper/paper.tex`, and committed.

This release preserves the existing **Lean 4 / Mathlib v4.11.0** formalization and the three-standard-axiom audit boundary. The historical verified release remains [v.0.0.6](https://github.com/jesusvilela/connection_laplacian_lean/releases/tag/v.0.0.6), tag commit `58fe64bdd7bf58030839eaf7f3ace8dc10b8bfb2` (18 October 2026). The verified main baseline for the present manuscript revision is `ae64b5e685760db82c835377a576031f056b50aa` (2 November 2026).

## Editorial and scholarly changes

- Use the author's full name and an explicit independent-researcher affiliation.
- Correct the MSC2020 codes to 05C50, 05C22, 68V20, and 68V15.
- Preserve the paper's references and explicitly avoid claims of novel discovery of classical signed-graph balance/nullity or spectral decomposition.
- Cite the historical v.0.0.6 verification baseline separately from newer explanatory revisions on main; pin the mathematical software dependencies.
- Expand AI provenance and author-understanding disclosures, retaining the original project methods note and theorem-by-theorem evidence map.
- Clarify that current Mathlib port work is **not** part of this release.

## Verification boundaries

- The original development and main-branch CI report compilation and an axiom audit against `propext`, `Classical.choice`, and `Quot.sound` for specified declarations. The public source audit forbids `sorry` and project-local new axioms.
- The independent comparator evidence concerns **seven historical end theorems and five separate cycle targets** at their archived tested commits, with negative controls. It does not automatically extend to every Lean theorem or to the newer Mathlib port.
- The exact cycle-to-general-graph spectral transfer remains **conditional** on a supplied vertex equivalence and both matrix reindexing identities.
- Numerical explorations are corroboration and counterexample search, not universal proof.

## Release checklist

1. Build the revised `paper/paper.tex` with the repository's existing `Rebuild paper PDF` workflow or an equivalent local `pdflatex` run (three passes).
2. Inspect output for unresolved references, errors, page truncation and correct typesetting; commit the regenerated `paper/paper.pdf` from the same TeX source.
3. Verify the original `lake build` workflow on the intended release commit.
4. Ensure `CITATION.cff` has the exact release tag, and add the actual release date only on publication.
5. Only then publish tag `v.0.0.7`; `.github/workflows/release.yml` attaches the **committed** PDF and does not rebuild it as an attachment.

The Hexagon submission must use the TeX source and may link to the GitHub formalization, with CC BY 4.0 for the manuscript.
