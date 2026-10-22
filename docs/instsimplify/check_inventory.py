#!/usr/bin/env python3
"""Check source provenance, rule identities, and source-return coverage.

This is a consistency check, not a replacement for the semantic source audit.
It deliberately does not infer rewrites or their guards from C++ text.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
PARTS = (("arithmetic_logic", 1, 2636), ("cmp_select", 2637, 5307),
         ("misc_intrinsics", 5308, 8040))


def source_returns(source: str) -> set[int]:
    # Preserve newline positions while removing comments and quoted literals.
    token = re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'')
    clean = token.sub(lambda m: "".join("\n" if c == "\n" else " " for c in m[0]), source)
    return {clean.count("\n", 0, m.start()) + 1 for m in re.finditer(r'\breturn\b', clean)}


def coverage_rows(raw):
    if isinstance(raw, list):
        return {int(r.get("line", r.get("return_line"))): r for r in raw}
    for key in ("coverage", "returns", "return_sites", "entries"):
        if key in raw:
            return coverage_rows(raw[key])
    return {int(k): v for k, v in raw.items() if str(k).isdigit()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", action="store_true", help="Allow incomplete inventory files")
    args = parser.parse_args()
    errors, entries = [], []
    pin = json.loads((HERE / "llvm-pin.json").read_text())
    for name, info in pin["sources"].items():
        data = (HERE / "upstream" / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != info["sha256"]:
            errors.append(f"Source hash mismatch: {name}")
    source = (HERE / "upstream/InstructionSimplify.cpp").read_text()
    returns = source_returns(source)
    for name, first, last in PARTS:
        inventory = HERE / "inventory" / f"{name}.json"
        coverage = HERE / "inventory" / f"{name}_coverage.json"
        if not inventory.exists() or not coverage.exists():
            if not args.draft:
                errors.append(f"Missing inventory or coverage: {name}")
            continue
        rules = json.loads(inventory.read_text())
        entries.extend(rules)
        local_ids = {r["id"] for r in rules}
        for rule in rules:
            for field in ("id", "start_line", "end_line", "function", "description", "opcodes", "extra", "kind", "returns"):
                if field not in rule:
                    errors.append(f"{rule.get('id')}: missing {field}")
            if not rule.get("opcodes"):
                errors.append(f"{rule['id']}: empty opcodes")
            for field in ("id", "function", "description", "kind"):
                if not isinstance(rule.get(field), str):
                    errors.append(f"{rule['id']}: {field} must be a string")
            for field in ("opcodes", "extra", "returns"):
                if not isinstance(rule.get(field), list):
                    errors.append(f"{rule['id']}: {field} must be a list")
            if not first <= rule["start_line"] <= rule["end_line"] <= last:
                errors.append(f"{rule['id']}: invalid source span")
            for line in rule["returns"]:
                if line not in returns:
                    errors.append(f"{rule['id']}: line {line} is not a source return")
        rows = coverage_rows(json.loads(coverage.read_text()))
        expected = {n for n in returns if first <= n <= last}
        if expected - rows.keys():
            errors.append(f"{name}: uncovered returns {sorted(expected - rows.keys())}")
        if rows.keys() - expected:
            errors.append(f"{name}: spurious return lines {sorted(rows.keys() - expected)}")
        for line, row in rows.items():
            entry_id = row.get("entry_id", row.get("id"))
            if entry_id and entry_id not in local_ids:
                errors.append(f"{name}:{line}: unknown entry {entry_id}")
            for extra_id in row.get("additional_entry_ids", []):
                if extra_id not in local_ids:
                    errors.append(f"{name}:{line}: unknown alternative {extra_id}")
        for rule in rules:
            for line in rule["returns"]:
                row = rows.get(line, {})
                recorded = [row.get("entry_id", row.get("id"))] + row.get("additional_entry_ids", [])
                if rule["id"] not in recorded:
                    errors.append(f"{name}:{line}: coverage does not record {rule['id']}")
                if not rule["start_line"] <= line <= rule["end_line"]:
                    errors.append(f"{rule['id']}: return {line} is outside its source span")
        print(f"{name}: {len(rules)} entries; {len(rows)}/{len(expected)} source return sites")
    ids = [r["id"] for r in entries]
    if len(ids) != len(set(ids)):
        errors.append("Duplicate rule IDs")
    for error in errors:
        print(f"ERROR: {error}")
    if errors:
        raise SystemExit(1)
    print(f"Consistency checks passed ({len(entries)} inventory entries).")


if __name__ == "__main__":
    main()
