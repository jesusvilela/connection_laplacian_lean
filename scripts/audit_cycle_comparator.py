#!/usr/bin/env python3
"""Fail if the cycle comparator harness loses coverage or weakens its guards.

This is a STATIC HARNESS INTEGRITY CHECK, not a substitute for running
leanprover/comparator with the actual challenge and solution exports.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
H = ROOT / "Hardening"
NAMES = [
    "Hardening.Cycle.periodic_charpoly",
    "Hardening.Cycle.antiperiodic_charpoly",
    "Hardening.Cycle.periodic_multiset",
    "Hardening.Cycle.antiperiodic_multiset",
    "Hardening.Cycle.mobius_graph_multiset",
]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
THEOREM = re.compile(r"(?m)^theorem\s+([A-Za-z][A-Za-z0-9_']*)\b")


def load(name: str) -> dict:
    return json.loads((H / name).read_text(encoding="utf-8"))


def check(condition: bool, msg: str) -> None:
    if not condition:
        raise SystemExit("cycle comparator harness: " + msg)


def theorem_names(file_name: str) -> list[str]:
    code = (H / file_name).read_text(encoding="utf-8")
    return ["Hardening.Cycle." + n for n in THEOREM.findall(code)]


def main() -> None:
    positive = load("config-cycle.json")
    nanoda = load("config-cycle-nanoda.json")
    check(positive["challenge_module"] == "Hardening.CycleChallenge",
          "unexpected main challenge module")
    check(positive["solution_module"] == "Hardening.CycleSolution",
          "unexpected main solution module")
    check(positive["theorem_names"] == NAMES, "expected five exact claims")
    check(set(positive["permitted_axioms"]) == ALLOWED, "axiom allowlist drift")
    check(theorem_names("CycleChallenge.lean") == NAMES, "challenge coverage drift")
    check(theorem_names("CycleSolution.lean") == NAMES, "solution coverage drift")
    check("sorry" not in (H / "CycleSolution.lean").read_text().split(
        "namespace Hardening.Cycle", 1)[1], "solution must be sorry-free")
    check("axiom " not in (H / "CycleSolution.lean").read_text().split(
        "namespace Hardening.Cycle", 1)[1], "solution must not declare axioms")
    check(nanoda["enable_nanoda"] is True, "dual-kernel config disabled")
    check({k: v for k, v in nanoda.items() if k != "enable_nanoda"} == positive,
          "nanoda config differs from positive comparator")

    negative_phase = load("config-cycle-negative-phase.json")
    negative_axiom = load("config-cycle-negative-axiom.json")
    for obj in (negative_phase, negative_axiom):
        check(obj["theorem_names"] == [NAMES[3]], "negative target drift")
        check(set(obj["permitted_axioms"]) == ALLOWED,
              "negative control axiom-allowlist drift")
    check(negative_phase["challenge_module"] ==
          "Hardening.CycleNegative.BadChallenge",
          "phase negative no longer points to tampered challenge")
    check(negative_phase["solution_module"] == "Hardening.CycleSolution",
          "phase negative solution drift")
    check(negative_axiom["challenge_module"] == "Hardening.CycleChallenge",
          "axiom negative challenge drift")
    check(negative_axiom["solution_module"] ==
          "Hardening.CycleNegative.BadSolution",
          "axiom negative no longer points to bad solution")
    check(theorem_names("CycleNegative/BadChallenge.lean") == [NAMES[3]],
          "phase negative theorem drift")
    check(theorem_names("CycleNegative/BadSolution.lean") == [NAMES[3]],
          "axiom negative theorem drift")
    bad_phase = (H / "CycleNegative/BadChallenge.lean").read_text()
    check("2 * j.val * Real.pi / n" in bad_phase, "phase perturbation removed")
    bad_solution = (H / "CycleNegative/BadSolution.lean").read_text()
    check("axiom smuggled_cycle_multiset" in bad_solution,
          "axiom-smuggling perturbation removed")

    print("cycle comparator config guard: five positive statements, "
          "two deliberate negative controls; JSON/source coverage consistent")
    print("NOTE: Comparator kernel replay and negative rejection MUST be "
          "run separately; the above is only a static guard.")


if __name__ == "__main__":
    main()
