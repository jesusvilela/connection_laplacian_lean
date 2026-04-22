# Licensing

This repository splits its license by artifact type so that code and paper
travel on their native conventions.

| Area | License | Files |
|------|---------|-------|
| Lean code, Python fuzzers, config, build scripts | Apache-2.0 | everything except `paper/` |
| Paper text, figures, bibliography | CC BY 4.0 | `paper/paper.tex`, `paper/paper.pdf` |

## Why

- **Apache-2.0 for code.** Matches Mathlib's own license, so contributions
  upstream carry no license-compatibility friction. The explicit patent grant
  protects both users and contributors.
- **CC BY 4.0 for the paper.** Standard for arXiv-style math papers; lets
  derivatives, translations, and classroom reuse proceed with attribution.

## Attribution template

For either layer:

> Jesús Vilela Jato, *Connection Laplacian — verified spectral/balance stack*
> (Lean 4 / Mathlib v4.11.0), 2026.
> DOI: 10.5281/zenodo.TBD — https://github.com/jesusvilela/connection_laplacian_lean

## Full license texts

- Apache-2.0 — `LICENSE` (full canonical text)
- CC BY 4.0 — `LICENSE-paper` (full canonical text from
  <https://creativecommons.org/licenses/by/4.0/legalcode.txt>)
- Copyright notice — `NOTICE` (Apache-2.0 §4(d) attribution)
