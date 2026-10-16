# Cycle-spectrum comparator challenge: scope, configuration, and evidence

## Independent *statement* target (five claims)

The following claims are separately stated in `CycleChallenge.lean`,
without importing the new `CycleMultiset` or `CycleGraphTransfer` proofs:

| Challenge statement | Mathematical obligation |
|---|---|
| `Hardening.Cycle.periodic_charpoly` | full real scalar-cycle characteristic polynomial, `n >= 3` |
| `Hardening.Cycle.antiperiodic_charpoly` | full real signed-cycle characteristic polynomial, `n >= 3` |
| `Hardening.Cycle.periodic_multiset` | exact scalar spectrum **as multiset**, not just support |
| `Hardening.Cycle.antiperiodic_multiset` | exact signed spectrum **as multiset**, including degeneracies |
| `Hardening.Cycle.mobius_graph_multiset` | full connection spectrum under **two explicit reindexing equalities** |

The challenge imports only `ConnectionLaplacian.CycleSpectrum` and
`Hardening.Compat` to identify the underlying graph and matrix
definitions, not the newly proved target spectral theorems.
`CycleSolution.lean` separately delegates to the verified proofs.
The challenge contains `sorry` **by design**, outside the production
theorem spine. The solution must contain none.

**Independence limitation:** the two transcripts, like the paper and
the implementation, were prepared in the same project context; this
is not an external human referee's independent transcription.
Comparator's statement-equivalence gate is useful nevertheless:
it compares the elaborated theorem *types* across modules and rejects
any unpermitted axioms or invalid proof terms when actually run.
Lean elaboration and `#print axioms` alone are **not** comparator replay.

## Files

- `Hardening/CycleChallenge.lean`: five expected statements
- `Hardening/CycleSolution.lean`: five proof delegations
- `Hardening/config-cycle.json`: standard comparator
- `Hardening/config-cycle-nanoda.json`: Lean + nanoda dual kernel
- `Hardening/CycleNegative/BadChallenge.lean`: changes signed
  eigenphase from anti-periodic `(2*k+1)` to periodic `(2*k)`; must be rejected
- `Hardening/CycleNegative/BadSolution.lean`: uses local axiom
  `smuggled_cycle_multiset`; must be rejected
- `Hardening/config-cycle-negative-{phase,axiom}.json`: negative gates
- `scripts/audit_cycle_comparator.py`: checks all five expected names,
  modules, configs, allowlists and negative-control payloads; **static only**

The seven original comparator-replayed theorems and their 2026-10-14
dual-kernel report are preserved separately in `Hardening/REPORT.md`
and `Hardening/config-nanoda.json`. Do not retroactively treat that
older run as proof of these new five statements.

## Reproduction (full replay)

Use the known-good Lean 4.11 target build, comparator pinned to
`leanprover/comparator` commit `e3dcf30`, the Lean 4.11 port of
`lean4export` at `5a9a355` using
`Hardening/lean4export-v4.11-port.diff`, and the `landrun` plus
`nanoda` binaries documented in the historical
[comparator report](REPORT.md#how-to-reproduce).

```bash
lake exe cache get
lake build
lake build Hardening.CycleChallenge Hardening.CycleSolution \
    Hardening.CycleNegative.BadChallenge Hardening.CycleNegative.BadSolution
python3 scripts/audit_cycle_comparator.py

# After constructing the pinned external binaries and verified sandbox:
COMPARATOR_LANDRUN=/path/to/landrun \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
COMPARATOR_NANODA=/path/to/nanoda_bin \
lake env /path/to/comparator Hardening/config-cycle-nanoda.json

# Negative controls must return nonzero exit status:
# 1. challenge mismatch:
lake env /path/to/comparator Hardening/config-cycle-negative-phase.json
# 2. unpermitted axiom:
lake env /path/to/comparator Hardening/config-cycle-negative-axiom.json
```

A faithful *high-trust* run additionally requires verified OS landlock
isolation (and ideally a restricted environment such as
`systemd-run --property=RestrictAddressFamilies=~AF_UNIX` as now
advised by upstream comparator), the unmodified pinned comparator,
a confirmed external kernel, and logged rejection of both negatives.
Do not treat `fake-landrun` as sandboxing. Use the toolchain's
actual `bin/` directory before `elan` shims on `PATH`.

GitHub Actions' `lake-build.yml` only checks source trust, Lean build,
axioms, harness JSON integrity, and successful elaboration of the
challenge/solution. It does **not** by itself execute comparator.

## Status ledger

- Historical seven-theorem comparator: **PASS** on 2026-10-14; dual
  Lean/nanoda kernels (see `REPORT.md`).
- All four cycle spectrum theorem statements: **Lean kernel VERIFIED**
  (PR #11) and explicitly `#print axioms` audited (PR #12).
- Five-theorem comparator challenge/solution: **new prepared harness**;
  record a new PASS only after actual comparator + both negative runs.
- Graph-level theorem: **proved conditional transport** requiring an
  explicit graph-vertex equivalence and the scalar/signed Laplacian
  reindexing equalities. **Still open:** constructing these two
  equalities for an arbitrary `ConnGraph` known abstractly to be a
  singly wrapped n-cycle.
- Strong wrap-parity iff and combinatorial mixed trace: **not implied**
  by the Fourier completeness work; remain independent obligations.

An immutable comparator run should record exact `git rev-parse HEAD`,
all toolchain/tool SHAs, `uname -r`, `landrun` enforcement check,
the challenge/solution module names, full acceptance/rejection logs,
and whether nanoda really ran. Archive these files before claiming an
external replay of the five new theorems.
