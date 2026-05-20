#!/usr/bin/env bash
# Runs all benchmarks and outputs results in github-action-benchmark JSON format.
# Adaptive sampling: warmup + minimum samples + extra samples until relative
# stddev (CV) drops below threshold, sample cap is hit, or time budget runs out.
# Reports median as `value` and stddev as `range` (rendered as error bars).
#
# Usage: ./run_benchmarks.sh [count] [pc] [min_iterations]
#   count:           tree size (default: 1000)
#   pc:              program counter param (default: 50)
#   min_iterations:  minimum samples per benchmark (default: 5)
#
# Tunable via env vars:
#   SAMPLES_MAX       max samples per benchmark (default: 30)
#   TIME_BUDGET_SECS  max wall time per benchmark, seconds (default: 180)
#   CV_THRESHOLD      target relative stddev in percent (default: 5.0)
#   WARMUP            warmup iterations to discard (default: 2)

set -euo pipefail

COUNT="${1:-1000}"
PC="${2:-50}"
SAMPLES_MIN="${3:-5}"

SAMPLES_MAX="${SAMPLES_MAX:-30}"
TIME_BUDGET_SECS="${TIME_BUDGET_SECS:-180}"
CV_THRESHOLD="${CV_THRESHOLD:-5.0}"
WARMUP="${WARMUP:-2}"

BENCHMARKS=(
  "add-fold-worklist"
  "add-fold-worklist-local"
  "add-zero-worklist"
  "add-zero-reuse-worklist"
  "mul-two-worklist"
  "add-fold-forwards"
  "add-zero-forwards"
  "add-zero-reuse-forwards"
  "mul-two-forwards"
  "add-zero-reuse-first"
  "add-zero-lots-of-reuse-first"
)

OUTPUT_FILE="${BENCHMARK_OUTPUT:-benchmark-results.json}"

lake build run-benchmarks >&2

median() {
  local sorted
  sorted=($(printf '%s\n' "$@" | sort -g))
  local n=${#sorted[@]}
  local mid=$((n / 2))
  if (( n % 2 == 1 )); then
    echo "${sorted[$mid]}"
  else
    echo "${sorted[$mid - 1]}" "${sorted[$mid]}" | awk '{printf "%.9f", ($1 + $2) / 2}'
  fi
}

stddev() {
  printf '%s\n' "$@" | awk '
    { x[NR]=$1; s+=$1 }
    END {
      if (NR < 2) { print "0"; exit }
      m = s/NR
      for (i=1;i<=NR;i++) v += (x[i]-m)*(x[i]-m)
      printf "%.9f", sqrt(v/(NR-1))
    }
  '
}

mean() {
  printf '%s\n' "$@" | awk '
    { s+=$1 }
    END { if (NR==0) {print "0"} else {printf "%.9f", s/NR} }
  '
}

cv_pct() {
  local m sd
  m=$(mean "$@")
  sd=$(stddev "$@")
  awk -v m="$m" -v sd="$sd" 'BEGIN { if (m+0==0) print "0"; else printf "%.4f", (sd/m)*100 }'
}

flt_lt() {
  awk -v a="$1" -v b="$2" 'BEGIN { exit !(a+0 < b+0) }'
}

run_one() {
  local bench="$1" out cs rs
  out=$(lake env run-benchmarks "$bench" "$COUNT" "$PC" 2>&1) || return 1
  cs=$(echo "$out" | sed -n 's/.*create time (s): \([0-9.]*\).*/\1/p')
  rs=$(echo "$out" | sed -n 's/.*rewrite time (s): \([0-9.]*\).*/\1/p')
  [ -n "$cs" ] && [ -n "$rs" ] && echo "$cs $rs"
}

echo "[" > "$OUTPUT_FILE"
first=true

for bench in "${BENCHMARKS[@]}"; do
  echo "Running benchmark: $bench (count=$COUNT, pc=$PC, min=$SAMPLES_MIN, max=$SAMPLES_MAX, budget=${TIME_BUDGET_SECS}s, cv<${CV_THRESHOLD}%, warmup=$WARMUP)" >&2

  for ((i = 1; i <= WARMUP; i++)); do
    run_one "$bench" >/dev/null || true
  done

  create_times=()
  rewrite_times=()
  start=$SECONDS

  for ((i = 1; i <= SAMPLES_MIN; i++)); do
    if pair=$(run_one "$bench"); then
      create_times+=("${pair% *}")
      rewrite_times+=("${pair#* }")
    else
      echo "  FAILED: $bench (sample $i)" >&2
    fi
  done

  while (( ${#rewrite_times[@]} < SAMPLES_MAX )); do
    elapsed=$(( SECONDS - start ))
    (( elapsed >= TIME_BUDGET_SECS )) && break

    if (( ${#rewrite_times[@]} >= 2 )); then
      cv_c=$(cv_pct "${create_times[@]}")
      cv_r=$(cv_pct "${rewrite_times[@]}")
      if flt_lt "$cv_c" "$CV_THRESHOLD" && flt_lt "$cv_r" "$CV_THRESHOLD"; then
        break
      fi
    fi

    if pair=$(run_one "$bench"); then
      create_times+=("${pair% *}")
      rewrite_times+=("${pair#* }")
    fi
  done

  for phase_name in create rewrite; do
    if [ "$phase_name" = "create" ]; then
      times=("${create_times[@]+"${create_times[@]}"}")
    else
      times=("${rewrite_times[@]+"${rewrite_times[@]}"}")
    fi

    [ ${#times[@]} -eq 0 ] && continue

    secs=$(median "${times[@]}")
    sd_secs=$(stddev "${times[@]}")
    cv=$(cv_pct "${times[@]}")

    value_ns=$(echo "$secs"    | awk '{printf "%.0f", $1 * 1000000000}')
    range_ns=$(echo "$sd_secs" | awk '{printf "%.0f", $1 * 1000000000}')

    if [ "$first" = true ]; then
      first=false
    else
      echo "," >> "$OUTPUT_FILE"
    fi

    cat >> "$OUTPUT_FILE" <<ENTRY
  {
    "name": "${bench}/${phase_name}",
    "unit": "ns",
    "value": $value_ns,
    "range": "± $range_ns",
    "extra": "count=$COUNT pc=$PC samples=${#times[@]} median=${secs}s stddev=${sd_secs}s cv=${cv}%"
  }
ENTRY

    echo "  $bench/$phase_name: median=${secs}s stddev=${sd_secs}s cv=${cv}% n=${#times[@]}" >&2
  done
done

echo "" >> "$OUTPUT_FILE"
echo "]" >> "$OUTPUT_FILE"

echo "Benchmark results written to $OUTPUT_FILE" >&2
