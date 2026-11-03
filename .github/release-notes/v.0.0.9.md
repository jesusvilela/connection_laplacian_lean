# v.0.0.9 — Hexagon TeX Live 2025 compatibility

**Scope: typesetting compatibility only.** This release addresses an error-like diagnostic in Hexagon's TeX Live 2025 private preview. The previous [v.0.0.8](https://github.com/jesusvilela/connection_laplacian_lean/releases/tag/v.0.0.8) release is immutable.

- After converting Appendix A to `longtable` in v.0.0.8, Hexagon's preview logged `ignored error: Infinite glue shrinkage found in box being split` at the `\end{longtable}` line, even though the PDF could still be compiled.
- The LaTeX project's [upstream issue latex3/latex2e#1907](https://github.com/latex3/latex2e/issues/1907) traces the diagnostic to two instances of `\vss` (infinitely shrinkable glue) inside `\LT@output`, exposed by page-mark extraction. The fix replaces those instances with bounded-shrink glue by applying two conditional `etoolbox` patches. On newer `longtable` implementations without `\vss` at those locations, the patches do nothing.
- This deliberately retains the 18-page layout and every row of the paper-to-Lean formalisation index.
- The revised PDF is built from the corresponding checked `paper/paper.tex` source, with restricted shell escape and a strict build-log audit. Re-run Hexagon's own preview with `paper.tex` from this release before final submission.

**Unchanged:** mathematical statements, assumptions, Lean proof files, Mathlib v4.11.0 pin, theorem-axiom audit boundaries, references, numerical data, and disclosure. The historic verification baseline remains [v.0.0.6](https://github.com/jesusvilela/connection_laplacian_lean/releases/tag/v.0.0.6). This update does **not** claim an additional mathematical verification round.

Release tag `v.0.0.9` should be created only after the final source and PDF are committed together, checked by CI, and visually reviewed. The GitHub release workflow attaches the committed PDF.
