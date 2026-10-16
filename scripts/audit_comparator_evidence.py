#!/usr/bin/env python3
"""Validate the immutable historical cycle replay archive, without replaying proofs."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / "Hardening/runs/38863604693"


def main():
    manifest = json.loads((ARCHIVE / "manifest.json").read_text(encoding="utf-8"))
    expected_files = {"positive.log", "negative-phase.log", "negative-axiom.log", "versions.txt"}
    if set(manifest["sha256"]) != expected_files:
        raise SystemExit("archive: missing or unexpected payload checksums")
    for name, digest in manifest["sha256"].items():
        if hashlib.sha256((ARCHIVE / name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"archive checksum mismatch: {name}")

    positive = (ARCHIVE / "positive.log").read_text(encoding="utf-8")
    exports = [line for line in positive.splitlines() if line.startswith("Exporting #[")]
    targets = {
        "periodic_charpoly", "antiperiodic_charpoly", "periodic_multiset",
        "antiperiodic_multiset", "mobius_graph_multiset",
    }
    if set(manifest["targets"]) != targets or len(exports) != 2:
        raise SystemExit("archive: five-target challenge/solution exports missing")
    for line, module in zip(exports, ("Hardening.CycleChallenge", "Hardening.CycleSolution")):
        found = re.findall(r"Hardening\.Cycle\.([a-z_]+)", line)
        if set(found) != targets or len(found) != 5 or not line.endswith("from " + module):
            raise SystemExit("archive: wrong theorem or transcript export")
    for marker in ("nanoda kernel accepts the solution",
                   "Lean default kernel accepts the solution", "Your solution is okay!"):
        if marker not in positive:
            raise SystemExit("archive: missing acceptance: " + marker)
    for filename, marker in (
        ("negative-phase.log", "Challenge and solution theorem statement do not match: 'Hardening.Cycle.antiperiodic_multiset'"),
        ("negative-axiom.log", "Illegal axiom detected: 'Hardening.Cycle.smuggled_cycle_multiset'"),
    ):
        if marker not in (ARCHIVE / filename).read_text(encoding="utf-8"):
            raise SystemExit("archive: missing expected rejection: " + filename)
    versions = (ARCHIVE / "versions.txt").read_text(encoding="utf-8")
    if "repository_commit=" + manifest["tested_commit"] not in versions:
        raise SystemExit("archive: tested commit mismatch")
    for tool in ("comparator", "lean4export", "landrun", "nanoda"):
        if not re.search(rf"(?m)^{tool}_sha=[0-9a-f]{{40}}$", versions):
            raise SystemExit("archive: missing tool identity: " + tool)
    print("archive PASS: four original SHA-256 payloads, five targets, two kernels, two expected rejections")
    print("Historical run 38863604693 only; no new proof replay or OS denial probe is inferred.")


if __name__ == "__main__":
    main()
