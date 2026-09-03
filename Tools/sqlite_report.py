"""Render the sqlite3 boards' JSON reports (Tools/sqlite_board.py schema).

`render` produces the Markdown used everywhere: the tools' own output, the CI
job summary and the sticky PR comment. `commit_message` produces the subject
and body of the baseline-update commit CI makes. Units are always named
(functions, globals, features) so counts never blur.
"""

from __future__ import annotations

UP, DOWN = "\U0001F7E2", "\U0001F534"  # green / red circle: GitHub has no colour
CAP = 200  # rows per section: a PR comment must stay under GitHub's 65536 chars
STATUS_WORD = {"ok": "supported"}  # the census's "ok" reads as "supported" in prose
PULL_NOTE = ("This commit was pushed by CI. Run git pull --rebase before pushing this "
             "branch again; do not force-push over it.")


def cell(text) -> str:
    return "`" + str(text).replace("|", "\\|").replace("`", "'") + "`"


def signed(n: int) -> str:
    return f"+{n} {UP}" if n > 0 else (f"{n} {DOWN}" if n < 0 else "+0")


def plural(n: int, unit: str) -> str:
    return f"{n} {unit if n != 1 else unit[:-1]}"


def table(header: list[str], rows: list[list[str]]) -> list[str]:
    numeric = ("count", "files", "total", "parsed")
    out = ["| " + " | ".join(header) + " |",
           "|" + "|".join("---:" if h in numeric else "---" for h in header) + "|"]
    out += ["| " + " | ".join(r) + " |" for r in rows[:CAP]]
    if len(rows) > CAP:
        more = ["...", f"and {len(rows) - CAP} more"] + [""] * (len(header) - 2)
        out.append("| " + " | ".join(more) + " |")
    return out


def details(title: str, body: list[str], open_: bool = False) -> list[str]:
    tag = "<details open>" if open_ else "<details>"
    return [f"{tag}<summary>{title}</summary>", ""] + body + ["", "</details>", ""]


def boards(*reports: dict):
    """Yield (corpus, label, board name, board) across the given reports."""
    for report in reports:
        for corpus, c in report.get("corpora", {}).items():
            for name, b in c["boards"].items():
                yield corpus, c["label"], name, b


def tier_deltas(d: dict) -> tuple[int, int]:
    """Change of the supported and parsed(-or-better) counts vs the baseline,
    from the delta's entries (current minus baseline)."""
    entries = d["improved"] + d["regressed"] + d["timeouts"]
    sup = sum((e["to"] == "supported") - (e["from"] == "supported") for e in entries)
    par = sum((e["to"] in ("supported", "parsed")) - (e["from"] in ("supported", "parsed"))
              for e in entries)
    return sup, par


def headline(score: dict, census: dict) -> list[str]:
    rows = []
    for corpus, c in score.get("corpora", {}).items():
        parts = [c["label"]]
        for name, b in c["boards"].items():
            n = b["counts"]
            sup, par, tot = n["supported"], n["supported"] + n["parsed"], len(b["items"])
            d = b.get("delta")
            if d is not None and not d["comparable"]:
                suffix = "(corpus changed)"
            elif d is not None:
                suffix = "(%s / %s)" % tuple(signed(x) for x in tier_deltas(d))
            else:
                suffix = ""
            parts.append(f"{name} {sup:>4} / {par:>4} / {tot:<4} {suffix}")
        rows.append(parts)
    for corpus, c in census.get("corpora", {}).items():
        label = c["label"]
        b = c["boards"]["features"]
        d = b.get("delta")
        parts = [f"features {label}"]
        if d is not None and not d["comparable"]:
            parts.append("(corpus changed)")
        for kind in ("op", "type", "attr"):
            k = b["kinds"][kind]
            change = ""
            if d is not None and d["comparable"]:
                up = sum(1 for e in d["improved"] if e["name"].startswith(kind + " "))
                down = sum(1 for e in d["regressed"] if e["name"].startswith(kind + " "))
                change = f" ({signed(up - down)})"
            parts.append(f"{kind}s {k['ok']}/{k['total']}{change}")
        rows.append(parts)
    width = max((len(r[0]) for r in rows), default=0)
    return ["```"] + [f"{r[0]:<{width}}  " + "   ".join(r[1:]) for r in rows] + ["```", ""]


def render(score: dict, census: dict) -> str:
    out = ["## sqlite3 scoreboard", ""] + headline(score, census)
    all_boards = list(boards(score, census))

    changed = [f"- {label} {name}: baseline digest `{b['delta']['digest']['baseline']}`, "
               f"run `{b['delta']['digest']['run']}`"
               for _, label, name, b in all_boards
               if b.get("delta") and not b["delta"]["comparable"]]
    if changed:
        note = ("Nothing was counted as a regression or an improvement, and no baseline "
                "was committed. If the new corpus is intended, regenerate the baselines "
                "with `--write-baseline` and commit them.")
        out += details(":warning: corpus changed (toolchain drift?) -- results not comparable",
                       changed + ["", note], open_=True)
    for _, label, name, b in all_boards:  # regressions first, open
        d = b.get("delta")
        if d and d["regressed"]:
            rows = [[cell(e["name"]), f"{e['from']} -> {e['to']}", cell(e["detail"])]
                    for e in d["regressed"]]
            out += details(f"{DOWN} {plural(len(rows), name)} regressed ({label})",
                           table([name[:-1], "status", "now hits"], rows), open_=True)
    for _, label, name, b in all_boards:
        d = b.get("delta")
        if d and d["timeouts"]:
            names = ", ".join(cell(e["name"]) for e in d["timeouts"][:CAP])
            out += details(f":warning: {plural(len(d['timeouts']), name)} timed out ({label}) "
                           "-- a warning, not a regression", [names], open_=True)
    for _, label, name, b in all_boards:  # improvements, collapsed
        d = b.get("delta")
        if d and d["improved"]:
            phrases = [f"{plural(n, name)} newly {STATUS_WORD.get(s[6:], s[6:])}"
                       for s, n in reversed(d["counts"].items()) if n]  # best tier first
            other = len(d["improved"]) - sum(d["counts"].values())
            phrases += [f"{plural(other, name)} recovered"] if other else []
            rows = [[cell(e["name"]), f"{e['from']} -> {e['to']}"] for e in d["improved"]]
            out += details(f"{UP} {', '.join(phrases)} ({label})",
                           table([name[:-1], "status"], rows))
    for _, label, name, b in all_boards:  # reference, collapsed
        if name == "features":
            rows = [[str(i["files"]), cell(k), cell(i["detail"])]
                    for k, i in sorted(b["items"].items(), key=lambda kv: -kv[1]["files"])
                    if i["status"] != "ok"]
            out += details(f"Unsupported features ({len(rows)}) -- {label}",
                           table(["files", "feature", "error"], rows))
    for corpus, c in score.get("corpora", {}).items():
        body = []
        for name, b in c["boards"].items():
            if b["distinct_errors"]:
                rows = [[str(len(n)), cell(err), cell(n[0])]
                        for err, n in b["distinct_errors"].items()]
                body += [f"**{name.capitalize()} failing, by error ({len(rows)} distinct)**", ""] \
                    + table(["count", "error", "e.g."], rows) + [""]
            if name == "functions" and b["blockers"]:
                rows = [[str(n), cell(blocker)] for blocker, n in list(b["blockers"].items())[:10]]
                body += [f"**Parsed but not supported ({b['counts']['parsed']} functions), "
                         "by blocker (top 10)**", ""] + table(["count", "blocked by"], rows) + [""]
            if name == "functions" and b.get("histogram"):
                rows = [[f"{size}+", str(oks), str(n), f"{oks / n:.0%}"]
                        for size, oks, n in b["histogram"]]
                body += ["**Parsed rate by function size (lines of generic MLIR)**", ""] \
                    + table(["size", "parsed", "total", "rate"], rows) + [""]
        if body:
            out += details(f"Blockers by function and global ({c['label']})", body)
    return "\n".join(out) + "\n"


def commit_message(score: dict, census: dict, run_url: str | None) -> str:
    """Subject: counts per corpus (the baseline diff shows the names). Body:
    regressions with the error each now hits, provenance, the pull note."""
    segments: dict[str, list[str]] = {}
    regressions: list[str] = []
    for _, label, name, b in boards(score, census):
        d = b.get("delta")
        if not d or not d["comparable"]:
            continue
        suffix = "" if name == "functions" else f" {name}"
        counts = [f"+{n} {status[6:]}{suffix}"
                  for status, n in reversed(d["counts"].items()) if n]  # best tier first
        if name == "features":
            counts = [f"+{sum(d['counts'].values())} features"] if any(d["counts"].values()) else []
        if d["regressed"]:
            word = plural(len(d["regressed"]), "regressions")
            counts.append(word if name == "functions" else f"{len(d['regressed'])} {name[:-1]} "
                          + word.split(" ", 1)[1])
        if counts:
            segments.setdefault(label, []).extend(counts)
        for e in d["regressed"]:
            unit = "" if name == "functions" else f"{name[:-1]} "
            regressions.append(f"{label} {unit}{e['name']}: {e['from']} -> {e['to']}: "
                               f"{e['detail']}")
    if not segments:
        summary = "function set changed"
    elif len(segments) == 1:
        summary = ", ".join(next(iter(segments.values())))
    else:
        summary = "; ".join(f"{label}: {', '.join(c)}" for label, c in segments.items())
    provenance = "Generated by the sqlite scoreboard workflow"
    provenance += f" from run {run_url}." if run_url else "."
    paragraphs = (["\n".join(regressions)] if regressions else []) + [provenance + "\n" + PULL_NOTE]
    return f"test: update sqlite3 baselines ({summary})\n\n" + "\n\n".join(paragraphs) + "\n"
