"""Shared mechanics of the sqlite3 boards: baselines, digests, deltas, exit codes.

Used by Tools/sqlite-scoreboard, Tools/mlir-feature-census, Tools/sqlite-report
and Tools/sqlite-ci. Nothing here knows about sqlite, corpora or veir-opt; it
only defines how a board's statuses are stored, compared and reported.

Baseline file (Test/sqlite3/<corpus>/<board>-baseline.txt)
    # corpus-digest: <16 hex>          digest of the chunk set the statuses are for
    <name>\\t<status>                   one line per item, sorted by name
  A status is one of the board's ranked statuses (scoreboard: fail < parsed <
  supported; census: missing < ok). "timeout" is never written: a timed-out
  item keeps its previous status, or is left out if it has none.

Report JSON (what --json-out writes; Tools/sqlite-report renders it)
    {"tool": str, "veir_opt": hash, "exit_code": int,
     "corpora": {<corpus>: {"label": str, "boards": {<board>: BOARD}}}}
    BOARD = {"digest": str, "items": {<name>: {"status": str, "detail": str, ...}},
             "counts": {<status>: int}, ...board-specific summaries...,
             "delta": DELTA | null}
    DELTA = {"comparable": bool, ["digest": {"baseline", "run"}],
             "improved": [ENTRY], "regressed": [ENTRY], "timeouts": [ENTRY],
             "added": [name], "removed": [name],
             "counts": {"newly_<status>": int}}
    ENTRY = {"name", "from", "to", "detail"}
  "detail" is the item's error class (normalized error) or blocker: informational,
  never compared.

Exit codes (every tool)
    0 unchanged  1 improvements only  2 any regression
    3 corpus digest mismatch (results not comparable)  64 tool error
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
VEIR_OPT = REPO_ROOT / ".lake" / "build" / "bin" / "veir-opt"
STORE = REPO_ROOT / ".lake" / "sqlite3-scoreboard"
BASELINE_DIR = REPO_ROOT / "Test" / "sqlite3"

EXIT_UNCHANGED, EXIT_IMPROVED, EXIT_REGRESSED, EXIT_NOT_COMPARABLE = 0, 1, 2, 3
EXIT_TOOL_ERROR = 64
TIMEOUT = "timeout"
# The sqlite3 corpora, primary first: directory name -> label used everywhere.
CORPORA = {"O0": "-O0+sroa"}


# ------------------------------------------------------------- digests --

def strip_machine_specific(data: bytes) -> bytes:
    """Canonical form of a chunk: the toolchain and target identity that
    mlir-translate embeds removed, so two machines with the same clang and
    mlir-translate majors hash a chunk identically."""
    import re
    data = re.sub(rb'(llvm\.ident|llvm\.target_triple|llvm\.data_layout) = "[^"]*"(, )?',
                  b"", data)
    marker = b"dlti.dl_spec = #dlti.dl_spec<"
    while (start := data.find(marker)) != -1:
        i, depth = start + len(marker) - 1, 0
        while i < len(data):
            if data[i:i + 1] == b'"':
                i += 1
                while i < len(data) and data[i:i + 1] != b'"':
                    i += 2 if data[i:i + 1] == b"\\" else 1
            elif data[i:i + 1] == b"<":
                depth += 1
            elif data[i:i + 1] == b">":
                depth -= 1
                if depth == 0:
                    break
            i += 1
        end = i + 1
        if data[end:end + 2] == b", ":
            end += 2
        data = data[:start] + data[end:]
    return data


def canonical_hash(path: Path) -> str:
    return hashlib.sha256(strip_machine_specific(path.read_bytes())).hexdigest()[:16]


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def corpus_digest(canonical_hashes: dict[str, str]) -> str:
    """Digest of a chunk set: sorted names and canonical contents."""
    h = hashlib.sha256()
    for name in sorted(canonical_hashes):
        h.update(name.encode())
        h.update(canonical_hashes[name].encode())
    return h.hexdigest()[:16]


# ----------------------------------------------------------- baselines --

def read_baseline(path: Path) -> tuple[str | None, dict[str, str]]:
    """(digest, {name: status}); tolerant of an old space-separated format."""
    digest, items = None, {}
    for line in path.read_text().splitlines():
        if line.startswith("# corpus-digest:"):
            digest = line.split(":", 1)[1].strip()
        elif line.strip() and not line.startswith("#"):
            name, status = line.rsplit("\t", 1) if "\t" in line else line.rsplit(None, 1)
            items[name] = status
    return digest, items


def write_baseline(path: Path, digest: str, statuses: dict[str, str]) -> None:
    """A timed-out item keeps its previous status (or is left out): a flaky
    run must never become the reference."""
    previous = read_baseline(path)[1] if path.exists() else {}
    lines = [f"# corpus-digest: {digest}"]
    for name, status in sorted(statuses.items()):
        if status == TIMEOUT:
            status = previous.get(name)
            print(f"warning: {name} timed out; baseline keeps {status or 'no entry'}",
                  file=sys.stderr)
            if status is None:
                continue
        lines.append(f"{name}\t{status}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")


def diff_baseline(path: Path, digest: str, items: dict[str, dict], rank: dict[str, int]) -> dict:
    """Compare a board's items ({name: {"status", "detail"}}) with its baseline.
    `rank` orders the statuses; moving down is a regression, up an improvement,
    to "timeout" a warning. Never gates on details."""
    delta = {"comparable": True, "improved": [], "regressed": [], "timeouts": [],
             "added": [], "removed": [],
             "counts": {f"newly_{s}": 0 for s in rank}}
    if not path.exists():
        raise SystemExit(f"no baseline at {path}; create it with --write-baseline")
    base_digest, baseline = read_baseline(path)
    if base_digest != digest:
        delta.update(comparable=False, digest={"baseline": base_digest, "run": digest})
        return delta
    for name, item in items.items():
        if name not in baseline:
            delta["added"].append(name)
            continue
        old, new = baseline[name], item["status"]
        if old == new:
            continue
        entry = {"name": name, "from": old, "to": new, "detail": item.get("detail", "")}
        if new == TIMEOUT:
            delta["timeouts"].append(entry)
        elif old == TIMEOUT or rank[new] > rank[old]:
            delta["improved"].append(entry)
            delta["counts"][f"newly_{new}"] += 1
        else:
            delta["regressed"].append(entry)
    delta["removed"] = sorted(set(baseline) - set(items))
    for key in ("improved", "regressed", "timeouts", "added"):
        delta[key].sort(key=lambda e: e["name"] if isinstance(e, dict) else e)
    return delta


def delta_code(delta: dict | None) -> int:
    if delta is None:
        return EXIT_UNCHANGED
    if not delta["comparable"]:
        return EXIT_NOT_COMPARABLE
    if delta["regressed"]:
        return EXIT_REGRESSED
    if delta["improved"] or delta["added"] or delta["removed"]:
        return EXIT_IMPROVED
    return EXIT_UNCHANGED


# --------------------------------------------------------------- cache --

def load_cache(path: Path, key: dict) -> dict:
    """Cached per-item results, valid only while `key` (e.g. the veir-opt hash
    and a schema version) is unchanged."""
    if not path.exists():
        return {}
    cached = json.loads(path.read_text())
    return cached.get("data", {}) if cached.get("key") == key else {}


def save_cache(path: Path, key: dict, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"key": key, "data": data}))


# ----------------------------------------------------------------- CLI --

def add_common_args(parser) -> None:
    parser.add_argument("--check-baseline", action="store_true",
                        help="compare with the baselines; exit 0 unchanged, 1 improvements "
                             "only, 2 any regression, 3 corpus digest mismatch, 64 tool error")
    parser.add_argument("--write-baseline", action="store_true",
                        help="write the baselines (after --check-baseline, in the same run)")
    parser.add_argument("--corpus", metavar="NAME", action="append",
                        help="restrict to this corpus (repeatable; default: all)")
    parser.add_argument("--json-out", type=Path, metavar="FILE",
                        help="write the full report as JSON to FILE "
                             "(schema: Tools/sqlite_board.py)")
    parser.add_argument("--delta-out", type=Path, metavar="FILE",
                        help="with --check-baseline: write only the deltas as JSON to FILE")
    parser.add_argument("--timeout", type=float, default=60, help="seconds per veir-opt run")
    parser.add_argument("-j", "--jobs", type=int, default=None,
                        help="parallel runs (default: CPUs)")


def finish(args, report: dict, quiet: bool = False) -> None:
    """Common ending of a board tool: JSON outputs, Markdown on stdout, exit code."""
    code = max([EXIT_UNCHANGED] + [delta_code(b.get("delta"))
                                   for c in report["corpora"].values()
                                   for b in c["boards"].values()])
    report["exit_code"] = code
    if args.json_out:
        args.json_out.write_text(json.dumps(report, indent=1))
    if args.delta_out:
        args.delta_out.write_text(json.dumps(
            {c: {b: board.get("delta") for b, board in corpus["boards"].items()}
             for c, corpus in report["corpora"].items()}, indent=1))
    if not quiet:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        import sqlite_report
        print(sqlite_report.render(*(
            (report, {}) if report["tool"] == "sqlite-scoreboard" else ({}, report))))
    sys.exit(code)


def run_main(main) -> None:
    """Tool errors exit with EXIT_TOOL_ERROR, never with a result code."""
    try:
        main()
    except SystemExit as e:
        if isinstance(e.code, str):
            print(f"{Path(sys.argv[0]).name}: {e.code}", file=sys.stderr)
            sys.exit(EXIT_TOOL_ERROR)
        raise
    except KeyboardInterrupt:
        sys.exit(EXIT_TOOL_ERROR)
    except Exception:
        import traceback
        traceback.print_exc()
        sys.exit(EXIT_TOOL_ERROR)
