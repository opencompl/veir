// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `select` whose true and false operands are the same value `x` always yields
// `x`, regardless of the condition: `(c ? x : x) -> x`. The `select` (and the
// dead condition) can be dropped.

"builtin.module"() ({
  "func.func"() <{function_type = (i1, i64) -> i64}> ({
  ^bb0(%c: i1, %x: i64):
    %r = "llvm.select"(%c, %x, %x) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: distinct arms, so the `select` must stay.
  "func.func"() <{function_type = (i1, i64, i64) -> i64}> ({
  ^bb0(%c: i1, %x: i64, %y: i64):
    %r = "llvm.select"(%c, %x, %y) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `select` is gone; the function returns its operand directly.
// CHECK:      ^{{.*}}(%{{.*}} : i1, %[[X:.*]] : i64):
// CHECK-NOT:  "llvm.select"
// CHECK:      "func.return"(%[[X]]) : (i64) -> ()

// The distinct-arm `select` survives.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1, %[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[SEL:.*]] = "llvm.select"(%[[C]], %[[NX]], %[[NY]])
// CHECK:      "func.return"(%[[SEL]]) : (i64) -> ()
