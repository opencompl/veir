// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(sub X, Y) eq X` is equivalent to `Y eq 0`: the shared `X`
// cancels out of the comparison.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i1, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %op = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.icmp"(%op, %x) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()

  // Negative case: the comparison's RHS is not the shared operand of the binop.
  "func.func"() <{function_type = (i64, i64, i64) -> i1, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %w: i64):
    %op = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.icmp"(%op, %w) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "func.return"(%r) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to `Y eq 0`.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[Z:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK:      %[[R:.*]] = "llvm.icmp"(%[[Y]], %[[Z]]) <{"predicate" = 0 : i64}> : (i64, i64) -> i1
// CHECK:      "func.return"(%[[R]]) : (i1) -> ()

// Unshared operand: the comparison is left intact.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NW:.*]] : i64):
// CHECK:      %[[NOP:.*]] = "llvm.sub"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.icmp"(%[[NOP]], %[[NW]]) <{"predicate" = 0 : i64}> : (i64, i64) -> i1
// CHECK:      "func.return"(%[[NR]]) : (i1) -> ()
