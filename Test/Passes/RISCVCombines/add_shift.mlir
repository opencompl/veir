// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `A + shl(0 - B, C)` is `A - shl(B, C)`: negating before the shift then adding is
// the same as shifting then subtracting.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %negb = "llvm.sub"(%zero, %b) : (i64, i64) -> i64
    %sh = "llvm.shl"(%negb, %c) : (i64, i64) -> i64
    %r = "llvm.add"(%a, %sh) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the shifted value is not a negation of anything (plain shl).
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %sh = "llvm.shl"(%b, %c) : (i64, i64) -> i64
    %r = "llvm.add"(%a, %sh) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to A - shl(B, C).
// CHECK:      ^{{.*}}(%[[A:.*]] : i64, %[[B:.*]] : i64, %[[C:.*]] : i64):
// CHECK:      %[[SH:.*]] = "llvm.shl"(%[[B]], %[[C]]) : (i64, i64) -> i64
// CHECK:      %[[R:.*]] = "llvm.sub"(%[[A]], %[[SH]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[R]]) : (i64) -> ()

// No negation: the add survives.
// CHECK:      ^{{.*}}(%[[NA:.*]] : i64, %[[NB:.*]] : i64, %[[NC:.*]] : i64):
// CHECK:      %[[NSH:.*]] = "llvm.shl"(%[[NB]], %[[NC]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.add"(%[[NA]], %[[NSH]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
