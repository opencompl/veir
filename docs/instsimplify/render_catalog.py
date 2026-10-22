#!/usr/bin/env python3
"""Render the reviewed source inventory and proof results as Markdown."""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def main():
    pin = json.loads((HERE / "llvm-pin.json").read_text())
    entries = []
    for name in ("arithmetic_logic", "cmp_select", "misc_intrinsics"):
        entries.extend(json.loads((HERE / "inventory" / f"{name}.json").read_text()))
    results = {}
    for path in sorted((HERE / "results").glob("*.json")):
        for row in json.loads(path.read_text()):
            if row["id"] in results:
                raise ValueError(f"Duplicate result for {row['id']}")
            results[row["id"]] = row
    ids = {e["id"] for e in entries}
    if results.keys() - ids:
        raise ValueError(f"Unknown result IDs: {results.keys() - ids}")
    counts = Counter()
    independent = Counter()
    by_kind = Counter()
    rows = []
    for entry in sorted(entries, key=lambda r: (r["start_line"], r["id"])):
        result = results.get(entry["id"], {"status": "pending", "reason": "Implementation assessment pending."})
        entry = {**entry, "kind": result.get("kind", entry["kind"])}
        status = result["status"]
        if status not in {"proved", "counterexample", "unsupported", "pending"}:
            raise ValueError(f"Invalid status: {entry['id']} {status}")
        files = result.get("files", [])
        for file in files:
            if not (ROOT / file).exists():
                raise ValueError(f"Missing file: {file}")
        if status == "proved" and (not files or not result.get("theorems")):
            raise ValueError(f"Proof without a file and theorem: {entry['id']}")
        counts[status] += 1
        if not result.get("covered_by"):
            independent[status] += 1
        by_kind[entry["kind"], status] += 1
        if files and not result.get("covered_by") and (status in {"proved", "counterexample"} or result.get("implemented", False)):
            counts["implemented"] += 1
            independent["implemented"] += 1
            by_kind[entry["kind"], "implemented"] += 1
        rows.append((entry, result))
    lines = ["# LLVM InstSimplify rewrites", "",
             f"Pinned LLVM commit: [`{pin['sha']}`](https://github.com/llvm/llvm-project/commit/{pin['sha']}).",
             "", "See [scope, methodology, and formalization limits](README.md). "
             "The source inventory was prepared by Luna agents; Lean implementations and proofs by Sol 6.1 agents. "
             "A rule's proof applies only to the domain explicitly recorded in its entry.", "",
             "## Counts", "",
             f"Independent implemented ports: **{independent['implemented']}**. "
             f"Independent ports proven `Pattern.Valid`: **{independent['proved']}**. "
             f"Independent counterexamples: **{independent['counterexample']}**. "
             "Caller entries marked `covered_by` are excluded from these totals. "
             "A source rule parameterized by opcode or operand order counts once; its concrete patterns and theorems are listed below.", "",
             "| Inventory kind | Entries | Independent implementations | Entries with proofs (including shared) | Counterexamples | Unsupported | Pending |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for kind in ("rewrite", "schema", "delegation"):
        total = sum(1 for e, _ in rows if e["kind"] == kind)
        values = [total] + [by_kind[kind, s] for s in ("implemented", "proved", "counterexample", "unsupported", "pending")]
        lines.append(f"| {kind} | " + " | ".join(map(str, values)) + " |")
    lines += ["", "Each row below is one audited source entry. Shared recursive algorithms and delegation sites "
              "are labeled separately to avoid treating dispatcher calls as additional peephole equations.", ""]
    base = f"https://github.com/llvm/llvm-project/blob/{pin['sha']}/{pin['source_path']}"
    for entry, result in rows:
        description = result.get("description", entry["description"])
        opcodes = result.get("opcodes", entry["opcodes"])
        extra = result.get("extra", entry["extra"])
        start, end = entry["start_line"], entry["end_line"]
        source = f"{base}#L{start}" + (f"-L{end}" if end != start else "")
        label = {"proved": "Succeeded — `Pattern.Valid` proven", "counterexample": "Counterexample",
                 "unsupported": "No complete standalone Puddle port — see the reason below",
                 "pending": "Pending — not counted as proven or unsupported"}[result["status"]]
        lines += [f"<a id=\"{entry['id'].lower()}\"></a>", "",
                  f"## {entry['id']} — `{entry['function']}`", "",
                  f"- **Original code:** [{pin['source_path']}:{start}–{end}]({source}). Kind: {entry['kind']}.",
                  f"- **Rewrite:** {description}",
                  "- **Matched/replaced opcodes:** " + ", ".join(f"`{op}`" for op in opcodes) + ".",
                  "- **Beyond opcode/constant/SSA matching:** " + ("Yes — " + "; ".join(extra) + "." if extra else "No."),
                  f"- **Result:** {label}."]
        if result.get("domain"):
            lines.append(f"- **Port/proof domain:** {result['domain']}")
        if result.get("files"):
            lines.append("- **Lean:** " + ", ".join(f"[{p}](../../{p})" for p in result["files"]) + ".")
        if result.get("theorems"):
            lines.append("- **Theorems:** " + ", ".join(f"`{t}`" for t in result["theorems"]) + ".")
        if result.get("covered_by"):
            covered_by = result["covered_by"]
            if isinstance(covered_by, str):
                covered_by = [covered_by]
            lines.append("- **Shared implementation:** " + ", ".join(f"[{i}](#{i.lower()})" for i in covered_by) + ". This caller is not an additional independent port.")
        if result.get("reason"):
            lines.append(f"- **Details / missing facilities:** {result['reason']}")
        if result.get("counterexample"):
            lines += ["", "```json", json.dumps(result["counterexample"], indent=2), "```"]
        lines.append("")
    pass_source = (f"https://github.com/llvm/llvm-project/blob/{pin['sha']}/"
                   "llvm/lib/Transforms/Scalar/InstSimplifyPass.cpp")
    lines += ["## Pass-driver dead-instruction deletion", "",
              f"- **Original code:** [InstSimplifyPass.cpp:48–66]({pass_source}#L48-L66). Kind: pass action / delegation.",
              "- **Rewrite:** Delete an instruction, and recursively its newly dead operands, when `isInstructionTriviallyDead` permits deletion. This also cleans up instructions after their uses are replaced by a simplification result.",
              "- **Matched/replaced opcodes:** Any opcode accepted by LLVM's dead-instruction predicate; deletion has no replacement opcode.",
              "- **Beyond opcode/constant/SSA matching:** Yes — use counts, side effects, memory/volatile behavior, target-library call information, and the pass worklist; unreachable blocks are skipped using the dominator tree.",
              "- **Result:** Cannot implement the full deletion action as a local Puddle result-replacement rule with the present validity contract. It requires a contextual unused-result and effect-safety certificate plus an instruction-erasure correctness theorem.",
              f"- **Accounting:** Documented separately from the {len(entries)} library source entries and excluded from the peephole implementation/proof totals.", ""]
    (HERE / "rewrites.md").write_text("\n".join(line.rstrip() for line in lines))
    statuses = ("implemented", "proved", "counterexample", "unsupported", "pending")
    summary = {"llvm_commit": pin["sha"], "entries": len(entries),
               **{status: counts[status] for status in statuses},
               "independent_ports": {status: independent[status] for status in statuses},
               "by_kind": {kind: {s: by_kind[kind, s] for s in ("implemented", "proved", "counterexample", "unsupported", "pending")}
                           for kind in ("rewrite", "schema", "delegation")}}
    (HERE / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
