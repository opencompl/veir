// RUN: python3 Tools/vsmith --memory-only --iterations 8 --workers 1 --seed 1785 | filecheck %s
// RUN: python3 Tools/vsmith --memory-only --riscv --no-mir-exec --iterations 8 --workers 1 --seed 1785 | filecheck %s
// RUN: %if llubi %{ python3 Tools/vsmith --memory-only --llubi --iterations 8 --workers 1 --seed 1785 | filecheck %s %}
// RUN: python3 %S/vsmith_checksum.py

// Memory-only cases must have concrete results, not just pass by refining UB
// or poison. The fixed seed covers packed structs, nested arrays, nonstandard
// integer strides, negative indices and both raw sentinel spellings.
// CHECK: no mismatches detected
// CHECK-NEXT: source: program output: 8
// CHECK-NEXT: optimized: program output: 8
