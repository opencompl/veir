// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Commuted form of `add_shift`: `shl(0 - B, C) + A -> A - shl(B, C)`, with the
// shifted (negated) value as the add's first operand.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %negb = "llvm.sub"(%zero, %b) : (i64, i64) -> i64
    %sh = "llvm.shl"(%negb, %c) : (i64, i64) -> i64
    %r = "llvm.add"(%sh, %a) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: no negation feeding the shift.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %sh = "llvm.shl"(%b, %c) : (i64, i64) -> i64
    %r = "llvm.add"(%sh, %a) : (i64, i64) -> i64
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
// CHECK:      %[[NR:.*]] = "llvm.add"(%[[NSH]], %[[NA]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
