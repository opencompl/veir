#!/usr/bin/env python3
"""Check captured AxiomAudit.lean output against the existing trusted baseline."""
from __future__ import annotations

import argparse
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ALLOWED = {
    "propext", "Classical.choice", "Quot.sound",
    "Veir.MemoryState.llvmLoad._native.bv_decide.ax_8✝",
    "Veir.MemoryState.loadByte64._native.bv_decide.ax_5✝",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="Captured output from lake env lean AxiomAudit.lean")
    args = parser.parse_args()
    output = args.output.read_text()
    expected = set(re.findall(r"^#print axioms (\S+)$", (HERE / "AxiomAudit.lean").read_text(), re.M))
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", output)
    reported = {name for name, _ in reports} | set(no_axioms)
    axioms = {axiom.strip() for _, group in reports for axiom in group.split(",") if axiom.strip()}
    errors = []
    if expected != reported:
        errors.append(f"Report mismatch: missing={sorted(expected - reported)}, extra={sorted(reported - expected)}")
    if axioms - ALLOWED:
        errors.append(f"Unexpected axioms: {sorted(axioms - ALLOWED)}")
    if re.search(r"(^|\n).*error:", output):
        errors.append("Lean reported an error")
    for error in errors:
        print("ERROR:", error)
    print(f"Audited {len(reported)} declarations; dependencies: {sorted(axioms)}")
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
