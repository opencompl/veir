#!/usr/bin/env bash
# llzk-diff.sh — compare veir-opt and llzk-opt output for an .mlir input.
#
# Exit codes:
#   0   identical (modulo normalization + allowlist)
#   1   differs after both tools succeeded
#   2   bad invocation / unreadable input
#   3   veir-opt failed
#   4   llzk-opt failed
#   77  skip (llzk-opt or lake missing — lit treats as UNRESOLVED/SKIP)
#
# Env / flags:
#   $LLZK_OPT             explicit path to llzk-opt (otherwise discovered on $PATH)
#   $VEIR_OPT             explicit path to veir-opt (otherwise use
#                         .lake/build/bin/veir-opt when present, then
#                         fall back to `lake exec veir-opt`)
#   $VEIR_DIFF_VERBOSE=1  print intermediate stages to stderr
#   $VEIR_DIFF_KEEP=1     don't delete intermediate temp files (debug aid)
#   --allowlist <file>    apply per-test fixed-string substitutions before diffing
#   --canonicalize        compare `veir-opt -p=felt-combine,dce` with
#                         `llzk-opt --canonicalize --mlir-print-op-generic`
#   --lower-first         first pass input through `llzk-opt --mlir-print-op-generic`
#                         (use when the input is in LLZK custom assembly; default
#                         assumes input is already in generic MLIR form)
#
# See docs/harness/GATES.md for the current protocol boundary and
# docs/harness/SOURCES.md for stale historical differential references.

set -euo pipefail

# --- args ---------------------------------------------------------------------
usage() {
  cat >&2 <<'USAGE'
usage: llzk-diff.sh <input.mlir> [--allowlist <file>] [--canonicalize] [--lower-first]
  Diffs normalized generic-MLIR output from veir-opt and llzk-opt.
  Default mode compares parse/print round-trips.
  --canonicalize compares `veir-opt -p=felt-combine,dce` against
  `llzk-opt --canonicalize --mlir-print-op-generic`.

  $LLZK_OPT or llzk-opt on $PATH selects the LLZK binary.
  $VEIR_OPT selects the VEIR binary; otherwise .lake/build/bin/veir-opt is
  used when present, with `lake exec veir-opt` as the fallback.
  $VEIR_DIFF_VERBOSE=1 streams intermediate stages to stderr.
  $VEIR_DIFF_KEEP=1 keeps intermediate temp files after exit.
USAGE
  exit 2
}

[[ $# -ge 1 ]] || usage
INPUT=""
ALLOWLIST=""
CANONICALIZE=0
LOWER_FIRST=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --allowlist) ALLOWLIST="${2:-}"; shift 2 ;;
    --canonicalize) CANONICALIZE=1; shift ;;
    --lower-first) LOWER_FIRST=1; shift ;;
    -h|--help) usage ;;
    *)
      if [[ -z "$INPUT" ]]; then
        INPUT="$1"
        shift
      else
        echo "unexpected extra argument: $1" >&2
        usage
      fi
      ;;
  esac
done

[[ -n "$INPUT" ]] || usage
[[ -r "$INPUT" ]] || { echo "input not readable: $INPUT" >&2; exit 2; }
INPUT_DIR="$(cd "$(dirname "$INPUT")" && pwd)" || {
  echo "input directory not readable: $(dirname "$INPUT")" >&2
  exit 2
}
INPUT="${INPUT_DIR}/$(basename "$INPUT")"

if [[ -n "$ALLOWLIST" ]]; then
  ALLOWLIST_DIR="$(cd "$(dirname "$ALLOWLIST")" 2>/dev/null && pwd || true)"
  if [[ -n "$ALLOWLIST_DIR" ]]; then
    ALLOWLIST="${ALLOWLIST_DIR}/$(basename "$ALLOWLIST")"
  fi
fi

# --- repo root ----------------------------------------------------------------
# llzk-diff.sh lives in <repo>/scripts/. veir-opt is invoked from <repo> so
# Lake finds the manifest when the fallback path is needed.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

# --- tool discovery -----------------------------------------------------------
LLZK_OPT="${LLZK_OPT:-$(command -v llzk-opt 2>/dev/null || true)}"
if [[ -z "${LLZK_OPT:-}" ]]; then
  echo "SKIP: llzk-opt not found (set \$LLZK_OPT or add to \$PATH)" >&2
  exit 77
fi
VEIR_OPT="${VEIR_OPT:-}"
if [[ -z "$VEIR_OPT" && -x "${REPO_ROOT}/.lake/build/bin/veir-opt" ]]; then
  VEIR_OPT="${REPO_ROOT}/.lake/build/bin/veir-opt"
fi
if [[ -z "$VEIR_OPT" ]] && ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: neither \$VEIR_OPT nor lake is available (cannot run veir-opt)" >&2
  exit 77
fi

# --- temp file setup ----------------------------------------------------------
TMPDIR_LOCAL="$(mktemp -d -t llzk-diff-XXXXXX)"
cleanup() {
  if [[ "${VEIR_DIFF_KEEP:-0}" == "1" ]]; then
    echo "kept intermediates in $TMPDIR_LOCAL" >&2
  else
    rm -rf "$TMPDIR_LOCAL"
  fi
}
trap cleanup EXIT

GENERIC="$TMPDIR_LOCAL/generic.mlir"
VEIR_OUT="$TMPDIR_LOCAL/veir.out.mlir"
LLZK_OUT="$TMPDIR_LOCAL/llzk.out.mlir"
VEIR_NORM="$TMPDIR_LOCAL/veir.norm.mlir"
LLZK_NORM="$TMPDIR_LOCAL/llzk.norm.mlir"
DIFF_OUT="$TMPDIR_LOCAL/diff.txt"

log() {
  # Don't use `[[ ... ]] && echo` here — that yields non-zero when verbose
  # is off, which under `set -e` aborts the whole script.
  if [[ "${VEIR_DIFF_VERBOSE:-0}" == "1" ]]; then
    echo "[llzk-diff] $*" >&2
  fi
}

# --- stage 1: optionally lower input via llzk-opt -----------------------------
if [[ "$LOWER_FIRST" -eq 1 ]]; then
  log "stage 1: lowering input via llzk-opt --mlir-print-op-generic"
  if ! "$LLZK_OPT" --mlir-print-op-generic "$INPUT" > "$GENERIC" 2>"$TMPDIR_LOCAL/llzk-lower.err"; then
    echo "FAIL: llzk-opt could not lower input" >&2
    cat "$TMPDIR_LOCAL/llzk-lower.err" >&2
    exit 4
  fi
else
  log "stage 1: skipped (--lower-first not set; assuming input is generic)"
  cp "$INPUT" "$GENERIC"
fi

# --- stage 2: round-trip through both -----------------------------------------
if [[ "$CANONICALIZE" -eq 1 ]]; then
  log "stage 2: canonicalize through veir-opt -p=felt-combine,dce and llzk-opt --canonicalize"
  if [[ -n "$VEIR_OPT" ]]; then
    VEIR_CMD=("$VEIR_OPT" -p=felt-combine,dce "$GENERIC")
  else
    VEIR_CMD=(lake exec veir-opt -p=felt-combine,dce "$GENERIC")
  fi
  LLZK_CMD=("$LLZK_OPT" --canonicalize --mlir-print-op-generic "$GENERIC")
else
  log "stage 2: round-trip through veir-opt and llzk-opt"
  if [[ -n "$VEIR_OPT" ]]; then
    VEIR_CMD=("$VEIR_OPT" "$GENERIC")
  else
    VEIR_CMD=(lake exec veir-opt "$GENERIC")
  fi
  LLZK_CMD=("$LLZK_OPT" --mlir-print-op-generic "$GENERIC")
fi

if ! "${VEIR_CMD[@]}" > "$VEIR_OUT" 2>"$TMPDIR_LOCAL/veir.err"; then
  echo "FAIL: veir-opt failed on input" >&2
  cat "$TMPDIR_LOCAL/veir.err" >&2
  exit 3
fi
if ! "${LLZK_CMD[@]}" > "$LLZK_OUT" 2>"$TMPDIR_LOCAL/llzk.err"; then
  echo "FAIL: llzk-opt failed on input" >&2
  cat "$TMPDIR_LOCAL/llzk.err" >&2
  exit 4
fi

# --- stage 3: normalize -------------------------------------------------------
# Conservative normalization (Python to get reliable regex backreferences):
#   - drop trailing whitespace; collapse runs of blank lines
#   - unquote attribute keys in property-attr position:
#       `<{"key" = ...}>` -> `<{key = ...}>`
#     (VEIR quotes attribute keys, LLZK doesn't)
#   - unquote attribute keys in discardable-attr position:
#       `}) {"key" = ...}` -> `}) {key = ...}`
#     (same VEIR-vs-LLZK gap; the regex is split because the prefix
#     context differs between property and discardable attr blocks)
#   - renumber SSA values in order of appearance: %anything -> %V<n>
#   - rename block labels: ^bb0 / ^4 / etc. -> ^B0 (handles both alpha
#     and numeric label prefixes), in-order-of-non-elided-appearance
#   - elide empty block headers `^name():` on a line by themselves
#     (VEIR emits an explicit empty block for the module body; LLZK doesn't).
#     Elision happens BEFORE label numbering so the surviving blocks
#     are numbered consistently across the two sides — otherwise a VEIR
#     region with empty wrapper-block headers would shift the surviving
#     block's label number.
#   - strip the cosmetic space before the type colon in block-arg
#     declarations: `^B0(%V0 : type)` -> `^B0(%V0: type)` (VEIR emits
#     the space, LLZK doesn't; both are valid generic-MLIR).
#   - strip the inner field annotation on FeltConstAttr:
#       `#felt<const N : <"name">>` -> `#felt<const N>`
#     (LLZK emits the inner form; VEIR emits the outer-only form
#     `#felt<const N> : !felt.type<"name">`. Both are valid; the
#     outer type annotation always survives and carries the field.)
#   - collapse empty region bodies: both `({    })` (VEIR's inline
#     whitespace form) and `({\n})` (LLZK's two-line form) become
#     `({})`. Functionally identical; cosmetically divergent.
# Other forms of equivalent-but-different output should go through the
# per-test allowlist, not this normalizer.
normalize() {
  local src="$1" dst="$2"
  python3 - "$src" "$dst" <<'PY'
import re, sys
src, dst = sys.argv[1], sys.argv[2]

ssa = {}
# Block labels are renumbered *scope-locally* — each region body gets
# its own counter starting at 0. This matches LLZK's printing
# convention (each region body's blocks start at ^bb0) and dodges the
# divergence where VEIR's global block counter and LLZK's per-region
# counter encode the same logical structure with different labels.
blk_stack = [{}]  # stack of {raw_label: normalized_label} per region scope

def sub_ssa(m):
    name = m.group(0)
    if name not in ssa:
        ssa[name] = f"%V{len(ssa)}"
    return ssa[name]

def sub_blk(m):
    name = m.group(0)
    top = blk_stack[-1]
    if name not in top:
        top[name] = f"^B{len(top)}"
    return top[name]

ssa_re = re.compile(r'%[A-Za-z0-9_.]+')
blk_re = re.compile(r'\^[A-Za-z0-9_]+')
# Attr-key quote stripping. Attribute keys can contain dots
# (`llzk.lang`, `function.allow_witness`), so the key character
# class includes `.`. Three contexts:
#   - `<{"key" = ` — property attrs, opening
#   - `, "key" = `  — continuation in either context
#   - `}) {"key" = ` — discardable attrs, opening (after region close).
#     Also matches at top-level (e.g., `"builtin.module"() ({...}) {"llzk.lang"}`).
key_quoted_open        = re.compile(r'<\{"([A-Za-z_][A-Za-z0-9_.]*)" = ')
key_quoted_comma       = re.compile(r', "([A-Za-z_][A-Za-z0-9_.]*)" = ')
key_quoted_discardable = re.compile(r'\) \{"([A-Za-z_][A-Za-z0-9_.]*)"')
# Empty block header: a line with only `^<label>():` (any whitespace).
# Matches the raw-label form (pre-renaming) so we can elide before the
# block-label counter advances.
empty_block_hdr_raw = re.compile(r'^\s*\^[A-Za-z0-9_]+\(\):\s*$')
# Cosmetic: VEIR emits `(%name : type)` for block args; LLZK emits
# `(%name: type)`. Both are valid generic-MLIR.
blockarg_space_colon = re.compile(r'(%[A-Za-z0-9_.]+) : ')
# FeltConstAttr inner field annotation. LLZK emits the inner form
# (`#felt<const 42 : <"babybear">>`); VEIR emits the outer-only
# form (`#felt<const 42> : !felt.type<"babybear">`). Both are
# valid; the outer annotation always survives downstream parsers.
# Strip the inner annotation to canonicalize.
felt_inner_annotation = re.compile(r'#felt<const (-?\d+) : <"[^"]+">>')

prev_blank = False
out_lines = []
with open(src) as f:
    for line in f:
        line = line.rstrip()
        # strip leading whitespace: MLIR generic-form indentation is purely
        # cosmetic (structure is fully parenthesized); VEIR indents 4 spaces
        # per level, LLZK 2.
        line = line.lstrip()
        if line == "":
            if prev_blank:
                continue
            prev_blank = True
            out_lines.append("")
            continue
        prev_blank = False
        # drop empty block header lines (VEIR-only artifact) BEFORE we
        # number their labels — otherwise the surviving labels' numbers
        # would diverge between VEIR and LLZK.
        if empty_block_hdr_raw.match(line):
            continue
        # unquote attribute keys (property-attr, continuation, discardable-attr)
        line = key_quoted_open.sub(lambda m: '<{' + m.group(1) + ' = ', line)
        line = key_quoted_comma.sub(lambda m: ', ' + m.group(1) + ' = ', line)
        line = key_quoted_discardable.sub(lambda m: ') {' + m.group(1), line)
        # strip cosmetic space-before-colon in block-arg type annotations
        line = blockarg_space_colon.sub(r'\1: ', line)
        # strip FeltConstAttr inner field annotation (LLZK emits it;
        # VEIR doesn't). The outer !felt.type<"name"> annotation
        # downstream always carries the field information.
        line = felt_inner_annotation.sub(r'#felt<const \1>', line)
        # block-label and SSA renaming — block labels use the current
        # region-scope counter (blk_stack top); SSA values use a flat
        # counter (LLZK also uses flat SSA numbering across a file
        # within generic form).
        line = blk_re.sub(sub_blk, line)
        line = ssa_re.sub(sub_ssa, line)
        # Region-scope stack: count `({` opens and `})` closes per line
        # so the block-label counter resets at every region body. The
        # generic-MLIR printer reliably uses `({` to open a region and
        # `})` to close it; we count both in case multiple appear on
        # the same line (unlikely but possible).
        for _ in range(line.count("({")):
            blk_stack.append({})
        for _ in range(line.count("})")):
            if len(blk_stack) > 1:
                blk_stack.pop()
        out_lines.append(line)

# --- post-process: empty region body collapse -----------------------------
# Both VEIR's inline whitespace form `({    })` and LLZK's two-line
# form `({\n})` become `({})`. We operate on the joined output so
# the cross-line case can be caught.
output = "\n".join(out_lines)
# Greedy match of `({` + any whitespace (including newlines) + `})`.
output = re.sub(r'\(\{\s*\}\)', '({})', output)
# Re-split for any further line-level handling (none today).
out_lines = output.split("\n")

with open(dst, 'w') as f:
    f.write("\n".join(out_lines))
    if out_lines and out_lines[-1] != "":
        f.write("\n")
PY
}

log "stage 3: normalize both outputs"
normalize "$VEIR_OUT" "$VEIR_NORM"
normalize "$LLZK_OUT" "$LLZK_NORM"

# --- stage 4: per-test allowlist (fixed-string substitution) ------------------
# Allowlist format, one per line:
#   "from-literal" -> "to-literal"   (optional trailing context for humans)
#
# Both <from> and <to> are matched as *fixed strings* (no regex). Applied to
# BOTH normalized files so equivalent forms collapse. Use this for documented
# divergences (e.g. VEIR's IntegerAttr representation of #felt.const<v>).
if [[ -n "$ALLOWLIST" ]]; then
  if [[ ! -r "$ALLOWLIST" ]]; then
    echo "WARN: allowlist $ALLOWLIST not readable; ignoring" >&2
  else
    log "stage 4: applying allowlist $ALLOWLIST"
    python3 - "$VEIR_NORM" "$LLZK_NORM" "$ALLOWLIST" <<'PY'
import re, sys
veir_path, llzk_path, allow_path = sys.argv[1], sys.argv[2], sys.argv[3]
rules = []
with open(allow_path) as f:
    for ln in f:
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        # "from" -> "to"  (anything after is ignored)
        m = re.match(r'^\s*"(.*?)"\s*->\s*"(.*?)"', ln)
        if m:
            rules.append((m.group(1), m.group(2)))
for path in (veir_path, llzk_path):
    with open(path) as f:
        s = f.read()
    for frm, to in rules:
        s = s.replace(frm, to)  # fixed-string, not regex
    with open(path, "w") as f:
        f.write(s)
PY
  fi
fi

# --- stage 5: diff ------------------------------------------------------------
log "stage 5: diff"
if diff -u --label "llzk-opt (normalized)" "$LLZK_NORM" --label "veir-opt (normalized)" "$VEIR_NORM" > "$DIFF_OUT" 2>&1; then
  echo "OK: outputs match (input: $INPUT)" >&2
  exit 0
else
  echo "DIFFER: $INPUT" >&2
  cat "$DIFF_OUT" >&2
  if [[ -n "$ALLOWLIST" ]]; then
    echo >&2
    echo "Hint: documented divergences belong in $ALLOWLIST; see docs/harness/GATES.md." >&2
  fi
  exit 1
fi
