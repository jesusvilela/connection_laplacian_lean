# Comparator hardening run — report

**Date:** 2026-10-13/14. **Verdict: PASS** — `"Your solution is okay!"`

The seven representative end theorems of the verified spine were
re-verified with `leanprover/comparator`
("a trustworthy judge for Lean proofs"): their elaborated statements match
the existing historical `Hardening/Challenge.lean` file actually configured
as comparator input, their proofs depend only on Lean's three standard
axioms, and every constant in the exported transitive closure
kernel-replays from scratch — **under a real landlock sandbox, with two
independent kernels** (Lean's own and nanoda) both accepting.

Separately, a fresh agent re-transcribed the seven statements from the
Lean sources without seeing the existing challenge file. The two sets
were reported token-identical after expanding the section variable:
`independent-transcription/TRANSCRIPTION.md` contains the fresh transcript,
and `EVIDENCE-MAP.md` records the comparison. This corroborates the
historical challenge; **the comparator did not run against the fresh
transcription**.

Two runs were performed:

1. **Primary (full trust posture), WSL2 Ubuntu 22.04, kernel
   6.18.33-microsoft-standard-WSL2 (landlock ABI v7):** comparator driven
   with real `landrun` 0.1.18 (built from `Zouuup/landrun` main, Go 1.24),
   every child process (`lake build`, `lean4export`, both kernels) executed
   inside the landlock sandbox. Sandbox enforcement was probed separately:
   writes outside granted paths are denied, execs outside granted paths are
   denied. Both the Lean kernel replay and the nanoda external kernel
   (built from `ammkrn/nanoda_lib` master, Rust) accepted the solution
   (`run-wsl-landrun-nanoda.log`). Negative controls 1 and 2 also reject
   under the real sandbox (`run-wsl-landrun-negative{1,2}.log`).
   A standalone nanoda check of the saved export reports
   *"Checked 16163 declarations with no typechecker errors"*
   (`nanoda-standalone.log`).
2. **Secondary (development path), Windows:** identical logic, but
   `landrun` replaced by upstream `fake-landrun.sh` (Windows has no
   landlock), no OS-level sandbox, builtin kernel replay only
   (`run-success.log`). Useful for iteration; not the trust claim.

## What was run

| Component | Version / state |
|---|---|
| Target project | this repo @ main (9ca3182), Lean v4.11.0, Mathlib v4.11.0 (cached oleans), `lake build` clean; WSL copy builds against the same (platform-independent) Mathlib oleans |
| comparator | `leanprover/comparator` @ master `e3dcf30`, toolchain v4.35.0, **binary unmodified** |
| lean4export | `leanprover/lean4export` @ master `5a9a355`, **ported to Lean v4.11.0** (see below), emits export format 3.1.0 |
| landrun | primary run: real landlock sandbox, landrun 0.1.18 from `Zouuup/landrun` main (Go); Windows run: `scripts/fake-landrun.sh`, sandbox NOT active |
| nanoda | primary run: `ammkrn/nanoda_lib` master (Rust), registered as comparator external kernel **and** run standalone; Windows run: not used |

Configuration: `Hardening/config.json` — challenge `Hardening.Challenge`
(statements + `sorry`), solution `Hardening.Solution` (aliases of the spine
theorems), permitted axioms `propext, Quot.sound, Classical.choice`.

## Results

### Positive run

- Challenge and solution statements agree on all 7 theorems
  (`Comparator.compareAt`, structural equality of elaborated types).
- `Comparator.checkAxioms`: transitive constant walk finds **only** the three
  permitted axioms. The saved export
  (`Hardening/solution-export.ndjson`, 1,320,201 NDJSON lines) contains
  exactly 3 axioms — `propext`, `Quot.sound`, `Classical.choice` (name-index
  resolution verified) — plus 10,324 theorems, 4,363 definitions, 469
  inductives, 4 quot constants, 16 opaques.
- `runBuiltinKernel`: `kernelEnv.replay` of the entire export into a fresh
  environment — **accepted**.
- Log: `Hardening/run-success.log`.

### Negative controls (the gate provably bites)

| Control | Input | Result |
|---|---|---|
| 1 — translation typo | `Hardening.Negative.BadChallenge`: coefficient `2` tampered to `3` in `trace_mul_scalar_signed_eq` | **REJECTED** — `Challenge and solution theorem statement do not match: 'Hardening.trace_mul_scalar_signed_eq'` (`run-negative1.log`) |
| 2 — axiom smuggling | `Hardening.Negative.BadSolution`: `mobius_charpoly_roots_eq_union` "proved" from local axiom `Hardening.smuggled_roots_union` | **REJECTED** — `Illegal axiom detected: 'Hardening.smuggled_roots_union'` (`run-negative2.log`) |

### Cross-checks

`lake env lean ConnectionLaplacian/AxiomAudit.lean` (the repo's own CI audit)
reports the same three axioms for all seven theorems.

## Local adaptations and their trust impact

1. **lean4export ported to v4.11.0** (43-line diff in `Export.lean` +
   toolchain pin). lean4export exists per-version only from v4.15.0 onward,
   and comparator@master parses format 3.1.0, so master's exporter was
   back-ported: `Std.HashMap` API (`emptyWithCapacity`→`empty`,
   disambiguation), `NameMap.alter`→`find?`/`insert`, `NameSet.union`→`++`,
   `List/Array.toJson`→`Json.arr`/`toJson`, `Expr.updateLet!` arity (4.11 has
   no `nonDep` argument), `String.ofList`→`String.mk` as the string-literal
   dependency constant. **Trust impact: none** — lean4export sits in the
   untrusted periphery by design; anything it gets wrong is caught by the
   kernel replay or the statement comparison.
2. **`Hardening/Compat.lean` stubs** for `String.ofList` and `eagerReduce`.
   comparator hardcodes a Lean-4.35 list of kernel builtin names to export;
   those two do not exist in a 4.11 environment, so inert stand-ins with
   those names keep the **comparator binary unmodified**. The stubs are
   imported by both challenge and solution (hence compared identical) and
   are ordinary safe definitions under kernel replay. They are used by no
   theorem.
3. **fake-landrun on the Windows run only** — the Windows pass used the
   upstream development shim (no OS-level isolation of build/export steps).
   The WSL pass is the authoritative one: real `landrun` with landlock
   enforced (write-deny and exec-deny probes confirmed the sandbox bites),
   and nanoda as a second, fully independent kernel. One WSL-specific
   detail: comparator grants exec only for the Lean toolchain dir and git,
   so `PATH` must put the toolchain `bin/` first (the elan shims live
   outside the granted exec paths; a shim-first PATH makes the sandboxed
   `lake` fail to exec — correctly).

## How to reproduce

```bash
# 1. Build this repo (Lean v4.11.0 via elan, mathlib cache)
lake exe cache get && lake build Hardening.Challenge Hardening.Solution

# 2. lean4export for Lean v4.11.0: clone leanprover/lean4export @ 5a9a355,
#    set lean-toolchain to leanprover/lean4:v4.11.0, apply the port in
#    Hardening/lean4export-v4.11-port.diff, then: lake build lean4export

# 3. comparator @ e3dcf30 (its own pinned v4.35.0): lake build comparator

# 4a. PRIMARY RUN (WSL2, real landrun + nanoda):
#     - landrun: git clone Zouuup/landrun && go build -o ~/bin/landrun ./cmd/landrun   (Go >= 1.24)
#     - nanoda:  git clone ammkrn/nanoda_lib && cargo build --release                  (Rust >= 1.78)
#     - copy this repo into WSL; symlink .lake/packages to the Windows
#       checkout's packages (oleans are platform-independent) or run
#       `lake exe cache get`; build Hardening.{Challenge,Solution}
#     - run with the toolchain bin FIRST on PATH (see note above):
PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.11.0/bin:$HOME/.elan/bin:/usr/bin:/bin" \
COMPARATOR_LANDRUN="$HOME/bin/landrun" \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export/.lake/build/bin/lean4export \
COMPARATOR_NANODA=/path/to/nanoda_lib/target/release/nanoda_bin \
lake env /path/to/comparator/.lake/build/bin/comparator Hardening/config-nanoda.json

# 4b. SECONDARY RUN (Windows, fake-landrun, no sandbox — dev only)
COMPARATOR_LANDRUN="$(pwd)/Hardening/landrun.cmd" \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export/.lake/build/bin/lean4export.exe \
lake env /path/to/comparator/.lake/build/bin/comparator.exe Hardening/config.json

# 5. Negative controls: swap in
#    Hardening/config-negative1-tampered-challenge.json
#    Hardening/config-negative2-smuggled-axiom.json   (both must FAIL)
```

## Phase 3 — gap-closure round (2026-10-15)

The three residual gaps in `Hardening/EVIDENCE-MAP.md` were attacked in
`findings/round8/`: an independent paper-only implementation (selftested,
8,887 checks) now supplies literal matrices that Lean itself verifies against
the formalization's definitions (`Hardening/ConventionAnchor.lean`,
`Hardening/ConventionBattery.lean`); a bounded-exhaustive n=8 sweep ran
7,246,819 configurations through that independent implementation with zero
failures; and a fresh-agent dual transcription confirmed the comparator
challenge is token-identical to the spine statements, surfacing four concrete
paper-adjacent bookkeeping items (see the evidence map's ledger). Details and
reproduction: `findings/round8/report.md`.

## Files added by this harness

- `Hardening/Compat.lean`, `Hardening/Challenge.lean`,
  `Hardening/Solution.lean` (+ `Hardening/Negative/*` controls) and a
  `lean_lib Hardening` entry in `lakefile.lean` — local, not part of the
  verified spine, not imported by `ConnectionLaplacian.lean`.
- `Hardening/`: config(s), landrun shim, run logs, saved export,
  `EVIDENCE-MAP.md`, this report, `ConventionAnchor.lean`,
  `ConventionBattery.lean` (generated), `independent-transcription/`.

The spine itself was not modified in any way.

## Addendum — later cycle-spectrum formalization (2026-10-16)

This report is an immutable account of the **historical seven-target
comparator run only**. Subsequent PRs #11 and #12 proved and audited the
full scalar and one-wrap signed cycle spectra over every `n >= 3`,
including repeated eigenvalues. A five-statement comparator transcript
(plus two new negative controls) has since been prepared in
[`CYCLE-COMPARATOR.md`](CYCLE-COMPARATOR.md).

**Do not reuse this report's "PASS", 1,320,201 export lines, nanoda
acceptance, or sandbox claim for the later spectrum theorems.** A new
full-replay run, with its own recorded commit and tool SHAs, sandbox
enforcement and negative-control logs, is required to make that claim.
