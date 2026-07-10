// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `x - (y + x)` cancels the two `x` terms, leaving `-y`, which is materialized
// as `0 - y`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %add = "llvm.add"(%y, %x) : (i64, i64) -> i64
    %s = "llvm.sub"(%x, %add) : (i64, i64) -> i64
    "func.return"(%s) : (i64) -> ()
  }) : () -> ()

  // Negative case: the minuend is not the `add`'s second operand, so no fold.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %w: i64):
    %add = "llvm.add"(%y, %x) : (i64, i64) -> i64
    %s = "llvm.sub"(%w, %add) : (i64, i64) -> i64
    "func.return"(%s) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The result is `0 - y`.
// CHECK:      ^{{.*}}(%{{.*}} : i64, %[[Y:.*]] : i64):
// CHECK:      %[[ZERO:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT: %[[NEG:.*]] = "llvm.sub"(%[[ZERO]], %[[Y]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NEG]]) : (i64) -> ()

// Unrelated minuend: the original `sub` survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NW:.*]] : i64):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NY]], %[[NX]]) : (i64, i64) -> i64
// CHECK:      %[[NSUB:.*]] = "llvm.sub"(%[[NW]], %[[NADD]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NSUB]]) : (i64) -> ()
