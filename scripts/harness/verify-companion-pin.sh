#!/usr/bin/env bash

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MODE="strict"
COMPANION_LLZK_LEAN=""

ACCEPTED_VEIR_COMMIT="a0bb2fc8e6d38ab068247dfc6506ba63f5feb953"
ACCEPTED_VEIR_SHORT="${ACCEPTED_VEIR_COMMIT:0:12}"
ACCEPTED_VEIR_REMOTE="https://github.com/project-llzk/veir.git"
ACCEPTED_VEIR_BRANCH="felt-review-structural-close"

FAIL=0
WARN=0

usage() {
  cat <<'USAGE'
usage: scripts/harness/verify-companion-pin.sh [--mode strict|exploratory] --companion-llzk-lean PATH

Verifies that the companion llzk-lean checkout pins VeIR to the accepted commit
in lakefile.toml, lake-manifest.json, and .lake/packages/VeIR, and that the
dependency checkout is clean.
USAGE
}

ok() {
  echo "PASS: $*"
}

warn() {
  echo "WARN: $*" >&2
  WARN=$((WARN + 1))
}

fail() {
  echo "FAIL: $*" >&2
  FAIL=$((FAIL + 1))
}

extract_lakefile_field() {
  local root="$1"
  local field="$2"
  awk -v wanted="$field" '
    function emit() {
      if (wanted == "rev") print rev
      else if (wanted == "git") print git
      else exit 1
    }
    /^\[\[require\]\]/ {
      if (in_req && name == "VeIR") { emit(); found = 1; exit }
      in_req = 1; name = ""; rev = ""; git = ""; next
    }
    /^\[\[/ {
      if (in_req && name == "VeIR") { emit(); found = 1; exit }
      in_req = 0
    }
    in_req && /^[[:space:]]*name[[:space:]]*=/ {
      line = $0; sub(/^[^"]*"/, "", line); sub(/".*/, "", line); name = line
    }
    in_req && /^[[:space:]]*git[[:space:]]*=/ {
      line = $0; sub(/^[^"]*"/, "", line); sub(/".*/, "", line); git = line
    }
    in_req && /^[[:space:]]*rev[[:space:]]*=/ {
      line = $0; sub(/^[^"]*"/, "", line); sub(/".*/, "", line); rev = line
    }
    END { if (!found && in_req && name == "VeIR") emit() }
  ' "${root}/lakefile.toml"
}

extract_manifest_field() {
  local root="$1"
  local field="$2"
  awk -v wanted="$field" '
    function json_value(line, key, value) {
      value = line
      sub(".*\"" key "\"[[:space:]]*:[[:space:]]*\"", "", value)
      sub("\".*", "", value)
      return value
    }
    function emit() {
      if (wanted == "url") print url
      else if (wanted == "type") print type
      else if (wanted == "rev") print rev
      else if (wanted == "inputRev") print inputRev
      else exit 1
    }
    /"packages"[[:space:]]*:/ { in_packages = 1 }
    in_packages && /\{/ { in_obj = 1; name = ""; url = ""; type = ""; rev = ""; inputRev = "" }
    in_obj && /"url"[[:space:]]*:/ { url = json_value($0, "url") }
    in_obj && /"type"[[:space:]]*:/ { type = json_value($0, "type") }
    in_obj && /"rev"[[:space:]]*:/ { rev = json_value($0, "rev") }
    in_obj && /"inputRev"[[:space:]]*:/ { inputRev = json_value($0, "inputRev") }
    in_obj && /"name"[[:space:]]*:/ {
      name = json_value($0, "name")
    }
    in_obj && /\}/ {
      if (name == "VeIR") { emit(); found = 1; exit }
      in_obj = 0
    }
    END { if (!found) exit 1 }
  ' "${root}/lake-manifest.json"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --mode)
      MODE="${2:-}"
      shift 2
      ;;
    --companion-llzk-lean)
      COMPANION_LLZK_LEAN="${2:-}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      fail "unknown argument: $1"
      usage
      exit 2
      ;;
  esac
done

case "$MODE" in
  strict|exploratory) ;;
  *)
    fail "invalid mode: ${MODE}"
    exit 2
    ;;
esac

echo "accepted VeIR pin: ${ACCEPTED_VEIR_COMMIT}"
echo "accepted VeIR source: ${ACCEPTED_VEIR_REMOTE} ${ACCEPTED_VEIR_BRANCH}"

local_head="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || true)"
if [[ "$local_head" == "$ACCEPTED_VEIR_COMMIT" ]]; then
  ok "local VeIR HEAD equals accepted pin ${ACCEPTED_VEIR_SHORT}"
else
  warn "local VeIR HEAD ${local_head:-<none>} differs from accepted pin ${ACCEPTED_VEIR_COMMIT}; checking companion against recorded pin"
fi

if [[ -z "$COMPANION_LLZK_LEAN" ]]; then
  fail "missing --companion-llzk-lean PATH"
  usage
else
  companion="$(cd "$ROOT" && cd "$COMPANION_LLZK_LEAN" 2>/dev/null && pwd || true)"
  if [[ -z "$companion" ]]; then
    fail "companion llzk-lean path is not readable: ${COMPANION_LLZK_LEAN}"
  else
    ok "companion llzk-lean path is ${companion}"

    lakefile_url="$(extract_lakefile_field "$companion" git 2>/dev/null || true)"
    lakefile_rev="$(extract_lakefile_field "$companion" rev 2>/dev/null || true)"
    manifest_url="$(extract_manifest_field "$companion" url 2>/dev/null || true)"
    manifest_type="$(extract_manifest_field "$companion" type 2>/dev/null || true)"
    manifest_rev="$(extract_manifest_field "$companion" rev 2>/dev/null || true)"
    manifest_input_rev="$(extract_manifest_field "$companion" inputRev 2>/dev/null || true)"

    if [[ "$lakefile_url" == "$ACCEPTED_VEIR_REMOTE" ]]; then
      ok "companion lakefile.toml uses accepted VeIR remote ${ACCEPTED_VEIR_REMOTE}"
    else
      fail "companion lakefile.toml VeIR git URL ${lakefile_url:-<none>} does not match ${ACCEPTED_VEIR_REMOTE}"
    fi

    if [[ "$lakefile_rev" == "$ACCEPTED_VEIR_COMMIT" ]]; then
      ok "companion lakefile.toml pins VeIR ${ACCEPTED_VEIR_SHORT}"
    else
      fail "companion lakefile.toml VeIR rev ${lakefile_rev:-<none>} does not match ${ACCEPTED_VEIR_COMMIT}"
    fi

    if [[ "$manifest_rev" == "$ACCEPTED_VEIR_COMMIT" ]]; then
      ok "companion lake-manifest.json pins VeIR ${ACCEPTED_VEIR_SHORT}"
    else
      fail "companion lake-manifest.json VeIR rev ${manifest_rev:-<none>} does not match ${ACCEPTED_VEIR_COMMIT}"
    fi

    if [[ "$manifest_input_rev" == "$ACCEPTED_VEIR_COMMIT" ]]; then
      ok "companion lake-manifest.json inputRev pins VeIR ${ACCEPTED_VEIR_SHORT}"
    else
      fail "companion lake-manifest.json VeIR inputRev ${manifest_input_rev:-<none>} does not match ${ACCEPTED_VEIR_COMMIT}"
    fi

    if [[ "$manifest_url" == "$ACCEPTED_VEIR_REMOTE" ]]; then
      ok "companion lake-manifest.json uses accepted VeIR remote ${ACCEPTED_VEIR_REMOTE}"
    else
      fail "companion lake-manifest.json VeIR URL ${manifest_url:-<none>} does not match ${ACCEPTED_VEIR_REMOTE}"
    fi

    if [[ "$manifest_type" == "git" ]]; then
      ok "companion lake-manifest.json records VeIR as a git dependency"
    else
      fail "companion lake-manifest.json VeIR type ${manifest_type:-<none>} is not git"
    fi

    if [[ -n "$lakefile_rev" && -n "$manifest_rev" && "$lakefile_rev" == "$manifest_rev" ]]; then
      ok "companion Lake files agree on VeIR ${lakefile_rev:0:12}"
    else
      fail "companion Lake files disagree on VeIR rev: lakefile=${lakefile_rev:-<none>} manifest=${manifest_rev:-<none>}"
    fi

    dep="${companion}/.lake/packages/VeIR"
    if [[ -d "$dep/.git" ]]; then
      dep_head="$(git -C "$dep" rev-parse HEAD 2>/dev/null || true)"
      if [[ "$dep_head" == "$ACCEPTED_VEIR_COMMIT" ]]; then
        ok "companion dependency checkout HEAD is ${ACCEPTED_VEIR_SHORT}"
      else
        fail "companion dependency checkout HEAD ${dep_head:-<none>} does not match ${ACCEPTED_VEIR_COMMIT}"
      fi

      if [[ -n "$manifest_rev" && "$dep_head" == "$manifest_rev" ]]; then
        ok "companion dependency checkout HEAD equals manifest rev"
      else
        fail "companion dependency checkout HEAD does not equal manifest rev ${manifest_rev:-<none>}"
      fi

      dep_status="$(git -C "$dep" status --short 2>/dev/null || true)"
      if [[ -z "$dep_status" ]]; then
        ok "companion dependency checkout is clean"
      else
        fail "companion dependency checkout is dirty:"
        printf '%s\n' "$dep_status" >&2
      fi
    else
      fail "companion dependency checkout missing at ${dep}"
    fi
  fi
fi

echo
echo "companion pin verification summary: ${FAIL} fail, ${WARN} warn, mode=${MODE}"
if [[ "$FAIL" -ne 0 ]]; then
  exit 1
fi
exit 0
