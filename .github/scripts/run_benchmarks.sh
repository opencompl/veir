#!/usr/bin/env bash
# Runs all benchmarks and outputs results in github-action-benchmark JSON format.
# Each benchmark is run multiple times; the median is reported to reduce noise.
# Usage: ./run_benchmarks.sh [count] [pc] [iterations]
#   count:      tree size (default: 1000)
#   pc:         program counter param (default: 50)
#   iterations: number of runs per benchmark for median (default: 5)

set -euo pipefail

COUNT="${1:-1000}"
PC="${2:-50}"
ITERATIONS="${3:-5}"

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

# Compute median of a list of numbers passed as arguments.
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

echo "[" > "$OUTPUT_FILE"
first=true

for bench in "${BENCHMARKS[@]}"; do
  echo "Running benchmark: $bench (count=$COUNT, pc=$PC, iterations=$ITERATIONS)" >&2

  create_times=()
  rewrite_times=()

  for ((i = 1; i <= ITERATIONS; i++)); do
    raw_output=$(lake exe run-benchmarks "$bench" "$COUNT" "$PC" 2>&1) || {
      echo "  FAILED: $bench (iteration $i)" >&2
      echo "  Output: $raw_output" >&2
      continue
    }

    rs=$(echo "$raw_output" | sed -n 's/.*rewrite time (s): \([0-9.]*\).*/\1/p')
    cs=$(echo "$raw_output" | sed -n 's/.*create time (s): \([0-9.]*\).*/\1/p')

    [ -n "$cs" ] && create_times+=("$cs")
    [ -n "$rs" ] && rewrite_times+=("$rs")
  done

  for phase_name in create rewrite; do
    if [ "$phase_name" = "create" ]; then
      times=("${create_times[@]+"${create_times[@]}"}")
    else
      times=("${rewrite_times[@]+"${rewrite_times[@]}"}")
    fi

    [ ${#times[@]} -eq 0 ] && continue

    secs=$(median "${times[@]}")

    # Convert seconds (float) to nanoseconds (integer) using awk
    value_ns=$(echo "$secs" | awk '{printf "%.0f", $1 * 1000000000}')

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
    "extra": "count=$COUNT pc=$PC iterations=$ITERATIONS median_${phase_name}=${secs}s"
  }
ENTRY

    echo "  $bench/$phase_name: ${secs}s (median of $ITERATIONS runs)" >&2
  done
done

echo "" >> "$OUTPUT_FILE"
echo "]" >> "$OUTPUT_FILE"

echo "Benchmark results written to $OUTPUT_FILE" >&2
