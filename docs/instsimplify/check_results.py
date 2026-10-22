#!/usr/bin/env python3
"""Validate result accounting and generate the Lean import/axiom audit targets.

Run after source auditing. This script checks bookkeeping; Lean must separately
compile the generated import target and the axiom audit.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def without_comments(text):
    # Lean nested block comments need a depth counter, not a non-greedy regex.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-pending", action="store_true")
    parser.add_argument("--generate", action="store_true")
    args = parser.parse_args()
    inventory = {}
    for name in ("arithmetic_logic", "cmp_select", "misc_intrinsics"):
        for row in json.loads((HERE / "inventory" / f"{name}.json").read_text()):
            assert row["id"] not in inventory, row["id"]
            inventory[row["id"]] = row
    results, errors = {}, []
    for path in sorted((HERE / "results").glob("*.json")):
        for row in json.loads(path.read_text()):
            if row["id"] in results:
                errors.append(f"Duplicate result: {row['id']}")
            results[row["id"]] = row
    if results.keys() - inventory.keys():
        errors.append(f"Unknown result IDs: {sorted(results.keys() - inventory.keys())}")
    pending = sorted(inventory.keys() - results.keys()) + sorted(
        r["id"] for r in results.values() if r["status"] == "pending")
    if pending and not args.allow_pending:
        errors.append(f"Unfinished entries ({len(pending)}): {pending}")
    modules, theorems = set(), set()
    files_to_ids = {}
    for row in results.values():
        status = row["status"]
        covered_by = row.get("covered_by", [])
        if isinstance(covered_by, str):
            covered_by = [covered_by]
        for other in covered_by:
            if other not in inventory:
                errors.append(f"Unknown shared implementation: {row['id']} -> {other}")
            elif status == "proved" and results.get(other, {}).get("status") != "proved":
                errors.append(f"Proven caller depends on an unfinished/unproved result: {row['id']} -> {other}")
        if row.get("kind", "rewrite") not in {"rewrite", "schema", "delegation"}:
            errors.append(f"Invalid kind correction: {row['id']}")
        if status not in {"proved", "counterexample", "unsupported", "pending"}:
            errors.append(f"Invalid status: {row['id']} {status}")
        if not row.get("reason") and status == "unsupported":
            errors.append(f"Unsupported without concrete reason: {row['id']}")
        if status == "counterexample" and not row.get("counterexample"):
            errors.append(f"Counterexample without witness: {row['id']}")
        if status == "proved" and (not row.get("files") or not row.get("theorems") or not row.get("domain")):
            errors.append(f"Incomplete proof result: {row['id']}")
        for rel in row.get("files", []):
            path = ROOT / rel
            if not path.is_file() or path.suffix != ".lean":
                errors.append(f"Missing Lean file: {row['id']} {rel}")
                continue
            files_to_ids.setdefault(rel, []).append(row["id"])
            # Checked diagnostic witnesses for unsupported domains are artifacts too;
            # importing/auditing them does not count them as successful ports.
            modules.add(rel[:-5].replace("/", "."))
        theorems.update(row.get("theorems", []))
    # A caller cannot justify itself through a cycle of shared implementations.
    def visit(identifier, path):
        if identifier in path:
            errors.append("Cyclic shared implementation: " + " -> ".join(path + [identifier]))
            return
        targets = results.get(identifier, {}).get("covered_by", [])
        if isinstance(targets, str):
            targets = [targets]
        for target in targets:
            visit(target, path + [identifier])

    for identifier in results:
        visit(identifier, [])
    # Include support files in the admission scan even when they are not result files.
    for path in (ROOT / "Veir/InstSimplify").glob("*.lean"):
        code = without_comments(path.read_text())
        if re.search(r"\b(sorry|admit|axiom)\b", code):
            errors.append(f"Admission or new axiom in {path.relative_to(ROOT)}")
        if not args.allow_pending and path.name.startswith("IS") and str(path.relative_to(ROOT)) not in files_to_ids:
            errors.append(f"Unaccounted rule file: {path.relative_to(ROOT)}")
    if args.generate and not errors:
        target = ROOT / "Veir/InstSimplify.lean"
        target.write_text("/- Generated by docs/instsimplify/check_results.py --generate. -/\n" +
                          "\n".join("import " + module for module in sorted(modules)) + "\n")
        audit = HERE / "AxiomAudit.lean"
        audit.write_text("import Veir.InstSimplify\n\n" +
                         "\n".join("#print axioms " + name for name in sorted(theorems)) + "\n")
        type_audit = HERE / "ProofTypeAudit.lean"
        type_audit.write_text("import Veir.InstSimplify\nimport Veir.InstSimplify.ProofAudit\n\n" +
                             "\n".join(
                                 f'audit_pattern_proofs "{row["id"]}" [{", ".join(row["theorems"])}]'
                                 for row in sorted(results.values(), key=lambda row: row["id"])
                                 if row["status"] == "proved") + "\n")
    for error in errors:
        print("ERROR:", error)
    counts = Counter(row["status"] for row in results.values())
    print(f"Results: {len(results)}/{len(inventory)}; statuses={dict(counts)}; pending={len(pending)}")
    print(f"Referenced Lean files: {len(files_to_ids)}; theorem declarations: {len(theorems)}")
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
