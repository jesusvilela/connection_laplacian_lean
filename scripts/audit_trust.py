#!/usr/bin/env python3
"""Fail CI if the verified Lean spine crosses an undeclared trust boundary."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
BANNED_TERMS = re.compile(r"\b(sorry|admit|native_decide)\b")
AXIOM_DECL = re.compile(r"(?m)^\s*axiom\s+")
AXIOM_ENTRY = re.compile(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", re.MULTILINE)
AXIOM_NONE = re.compile(r"'([^']+)' does not depend on any axioms", re.MULTILINE)
AUDITED_NAME = re.compile(r"(?m)^\s*#print axioms\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")


def without_comments(source: str) -> str:
    """Remove nested Lean comments while retaining strings and newlines."""
    out: list[str] = []
    i = depth = 0
    in_string = False
    while i < len(source):
        pair = source[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif in_string:
            out.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                out.append(source[i + 1])
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                break
            out.append("\n")
            i = end + 1
        else:
            out.append(source[i])
            if source[i] == '"':
                in_string = True
            i += 1
    if depth:
        raise ValueError("unterminated block comment")
    return "".join(out)


def audit_sources(root: Path) -> None:
    failures: list[str] = []
    files = [root / "ConnectionLaplacian.lean", *sorted((root / "ConnectionLaplacian").glob("*.lean"))]
    for path in files:
        clean = without_comments(path.read_text(encoding="utf-8"))
        for match in BANNED_TERMS.finditer(clean):
            failures.append(f"{path}:{clean.count(chr(10), 0, match.start()) + 1}: forbidden {match.group(1)}")
        for match in AXIOM_DECL.finditer(clean):
            failures.append(f"{path}:{clean.count(chr(10), 0, match.start()) + 1}: user axiom declaration")
    if failures:
        raise SystemExit("\n".join(failures))
    print(f"source audit: {len(files)} files, no sorry/admit/native_decide/user axioms")


def audit_axiom_output(path: Path, root: Path) -> None:
    """Require each requested #print to appear, with no undeclared axioms.

    Silently omitting a requested theorem must FAIL rather than being
    mistaken for broad proof coverage.
    """
    output = path.read_text(encoding="utf-8")
    requested = AUDITED_NAME.findall(
        (root / "ConnectionLaplacian/AxiomAudit.lean").read_text(encoding="utf-8")
    )
    if not requested or len(set(requested)) != len(requested):
        raise SystemExit("axiom audit: no declarations or duplicate #print names")
    with_axioms = AXIOM_ENTRY.findall(output)
    without_axioms = AXIOM_NONE.findall(output)
    recorded = [name for name, _ in with_axioms] + without_axioms
    missing = set(requested) - set(recorded)
    extra = set(recorded) - set(requested)
    duplicates = sorted({x for x in recorded if recorded.count(x) > 1})
    if missing or extra or duplicates:
        raise SystemExit(
            "axiom audit: incomplete/mismatched coverage:"
            f" missing={sorted(missing)}, extra={sorted(extra)},"
            f" duplicate={duplicates}"
        )
    unexpected: set[str] = set()
    for _, body in with_axioms:
        used = {item.strip() for item in body.split(",") if item.strip()}
        unexpected.update(used - ALLOWED_AXIOMS)
    if unexpected:
        raise SystemExit("axiom audit: unexpected axioms: " + ", ".join(sorted(unexpected)))
    print(f"axiom audit: {len(recorded)} / {len(requested)} requested theorems;"
          f" only {sorted(ALLOWED_AXIOMS)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--axiom-output", type=Path)
    args = parser.parse_args()
    audit_sources(args.root)
    if args.axiom_output:
        audit_axiom_output(args.axiom_output, args.root)


if __name__ == "__main__":
    main()
