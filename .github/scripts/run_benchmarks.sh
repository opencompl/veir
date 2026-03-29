#!/usr/bin/env bash
# Runs all benchmarks and outputs results in github-action-benchmark JSON format.
# Usage: ./run_benchmarks.sh [count] [pc]
#   count: tree size (default: 1000)
#   pc:    program counter param (default: 50)

set -euo pipefail

COUNT="${1:-1000}"
PC="${2:-50}"

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

echo "[" > "$OUTPUT_FILE"
first=true

for bench in "${BENCHMARKS[@]}"; do
  echo "Running benchmark: $bench (count=$COUNT, pc=$PC)" >&2

  # Capture benchmark output
  # Output format from Benchmarks.lean time function: "{name} time (s): {float}"
  raw_output=$(lake exe run-benchmarks "$bench" "$COUNT" "$PC" 2>&1) || {
    echo "  FAILED: $bench" >&2
    echo "  Output: $raw_output" >&2
    continue
  }

  # Extract "rewrite time (s): <float>" -- this is the main metric we care about
  rewrite_secs=$(echo "$raw_output" | sed -n 's/.*rewrite time (s): \([0-9.]*\).*/\1/p')
  create_secs=$(echo "$raw_output" | sed -n 's/.*create time (s): \([0-9.]*\).*/\1/p')

  if [ -z "$rewrite_secs" ] && [ -z "$create_secs" ]; then
    echo "  Could not parse timing for $bench, skipping" >&2
    echo "  Raw output: $raw_output" >&2
    continue
  fi

  # Emit separate entries for create and rewrite phases
  for phase_name in create rewrite; do
    if [ "$phase_name" = "create" ]; then
      secs="$create_secs"
    else
      secs="$rewrite_secs"
    fi
    [ -z "$secs" ] && continue

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
    "extra": "count=$COUNT pc=$PC ${phase_name}=${secs}s"
  }
ENTRY

    echo "  $bench/$phase_name: ${secs}s" >&2
  done
done

echo "" >> "$OUTPUT_FILE"
echo "]" >> "$OUTPUT_FILE"

echo "Benchmark results written to $OUTPUT_FILE" >&2
