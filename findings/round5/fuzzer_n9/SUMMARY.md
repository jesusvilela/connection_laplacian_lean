# FUZZER-N9 — partial run, truncated

**Date:** 2026-04-22. **Status:** Agent exited before completing the full sweep.

## Actual coverage (from `run.log`)

| n | mode | graphs processed | configs | max_charpoly_rel_diff |
|---|------|------------------|---------|------------------------|
| 2 | exhaustive | 2 / 2 | 3 | 0.00 |
| 3 | exhaustive | 4 / 4 | 15 | 0.00 |
| 4 | exhaustive | 11 / 11 | 163 | 0.00 |
| 5 | exhaustive | 30+ / 34 | 1,227+ | 0.00 |

Log output truncated at n=5 graph 30/34. No n=6,7,8,9 data collected.

## Results on n ≤ 5 exhaustive slice

- `max_charpoly_rel_diff = 0.00e+00` — no numerical drift at n ≤ 5 (as expected; the n=8 regime is where float-polynomial condition numbers bite).
- No new negative evidence against any landed theorem in L9-L15.
- Track B new-category identities (`NEW_walk_h1_balance`, `NEW_tree_charpoly`, `NEW_sig_ker_basis`, `NEW_cover_eigenvec_lift`) all passing on the n ≤ 5 slice per the log (`det`/`ld`/`sp` diagnostic columns all at expected noise floor).

## Why truncated

The agent returned a text-only final message ("Monitor armed...") without producing `results.json` or `SUMMARY.md` artifacts, though it did write `fuzz_n9.py` and `run.log` to disk. Plausible causes: agent hit a time budget before the n ≥ 6 phase completed, or the final report step was cut off.

## Artifacts

- `fuzz_n9.py` — the port from `fuzz_n8.py` with high-precision arithmetic path and Track-B new-category tests.
- `run.log` — partial stdout up to n=5 graph 30/34.
- `SUMMARY.md` — this file.

## Follow-up (R6)

Re-run `fuzz_n9.py` standalone to completion, target n ≤ 7 with the improved arithmetic path to see whether the n=7 charpoly noise (9.1e-6 under the n=8 script) tightens under `mpmath`/`longdouble`. Full n=9 push deferred until the Track-B identities have a definitive pass across n ≤ 7.

## Net

No negative evidence discovered; no new findings from the partial run. The identities tested so far at n ≤ 5 all hold.
