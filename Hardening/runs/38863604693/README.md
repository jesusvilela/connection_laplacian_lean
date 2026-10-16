# Cycle comparator replay, 2026-10-16

Source: [Actions run 38863604693](https://github.com/jesusvilela/connection_laplacian_lean/actions/runs/38863604693),
job 116851409968, artifact 12029793515 (`cycle-comparator-evidence`).
The four artifact files are copied without changes; SHA-256 checksums are
in `manifest.json`. The ZIP digest is the digest published by GitHub,
not a locally recomputed ZIP digest. `job.log` is the separately retrieved,
decoded GitHub job transcript. It is supporting context, not one of the
four checksummed artifact files.

Archive logs retain their original whitespace; the local attributes disable
text conversion and whitespace linting for those preserved transcripts.

The tested commit was GitHub's temporary PR #13 merge commit
`380d09507df219a8a04fd7f63feb0a43c610aaff`, with PR head
`e572a8c34212fd11471042d87bcd9cee5537bf48`; the later actual merge
onto main is `b92bcb643643676d14dcdc0694e4af36c96eaaf3`.
These are distinct identities. This is evidence for that run, not an
assertion that every later repository commit was replayed.

| File | Observed result |
|---|---|
| `positive.log` | All five `Hardening.Cycle` targets exported from both transcripts; nanoda and Lean accept; comparator concludes `Your solution is okay!` |
| `negative-phase.log` | Nonzero run; `antiperiodic_multiset` statement does not match the tampered periodic phase |
| `negative-axiom.log` | Nonzero run; illegal axiom `Hardening.Cycle.smuggled_cycle_multiset` detected |
| `versions.txt` | Exact tested commit, UTC time, OS, Lean/Lake and all four external-tool SHAs |

The job transcript shows the pinned real `landrun` binary being built and
selected by `COMPARATOR_LANDRUN`; it records no standalone forbidden-read
or forbidden-write enforcement probe. Report the real-landrun invocation
and successful replay, while preserving this OS-enforcement-evidence limit.
It also does not establish the additional `AF_UNIX` restriction suggested
by upstream comparator. The original historical WSL denial probe is
separate evidence and does not fill this run's gap.

The fifth target assumes a vertex equivalence and two matrix equalities.
Replay checks that conditional statement; it does not construct a concrete
`ConnGraph` cycle identification, prove L14's reverse implication, or prove
the combinatorial mixed trace identity.

Run `python scripts/audit_comparator_evidence.py` from the repository root
to verify the preserved files and acceptance/rejection markers. This is
archive validation; fresh proof replay uses the workflow described in
[`CYCLE-COMPARATOR.md`](../../CYCLE-COMPARATOR.md).
