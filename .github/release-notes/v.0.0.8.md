# v.0.0.8 — typesetting improvements for the Hexagon manuscript

Presentation-only update of the 3 November 2026 paper, continuing from [v.0.0.7](https://github.com/jesusvilela/connection_laplacian_lean/releases/tag/v.0.0.7).

- Convert Appendix A's unbreakable formalisation-index `tabular` to a page-breaking `longtable`, with a repeated header where a page break occurs.
- Improve line breaking of Lean identifiers and source filenames in the table while preserving their spelling and the statement-to-file correspondence.
- Rebuild the committed `paper/paper.pdf` from the revised `paper/paper.tex`.
- Prevent the almost-empty appendix page and isolated author-contact page observed in the first Hexagon PDF preview.

**Mathematical scope and trust floor unchanged.** No Lean source, theorem, graph construction, proof dependency, axiom audit, mathematical result, bibliography entry, or numerical experiment is modified. The formalization remains pinned to Lean 4 / Mathlib v4.11.0. The earlier archived verification baseline is [v.0.0.6](https://github.com/jesusvilela/connection_laplacian_lean/releases/tag/v.0.0.6). The cycle-to-general-graph matrix transfer still carries its explicit hypotheses.

The matching PDF is the committed `paper/paper.pdf`; the `Create release` GitHub workflow attaches that reviewed artifact and checks that the TeX compiles. Readers may use the release-tagged `paper/paper.tex` for exact reproducibility.
