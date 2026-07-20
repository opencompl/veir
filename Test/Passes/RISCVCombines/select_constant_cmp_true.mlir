// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `select` with a constant-`1` condition always picks the true operand:
// `(1 ? x : y) -> x`. The `select` is erased and its uses forwarded to `x`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%t: i64, %f: i64):
    %c = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: a non-constant condition leaves the `select` in place.
  "func.func"() <{function_type = (i1, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%c: i1, %t: i64, %f: i64):
    %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `select` is gone; the true operand is returned directly.
// CHECK:      ^{{.*}}(%[[T:.*]] : i64, %{{.*}} : i64):
// CHECK-NOT:  "llvm.select"
// CHECK:      "func.return"(%[[T]]) : (i64) -> ()

// The non-constant-condition `select` survives.
// CHECK:      ^{{.*}}(%[[C:.*]] : i1, %[[NT:.*]] : i64, %[[NF:.*]] : i64):
// CHECK:      %[[SEL:.*]] = "llvm.select"(%[[C]], %[[NT]], %[[NF]])
// CHECK:      "func.return"(%[[SEL]]) : (i64) -> ()
