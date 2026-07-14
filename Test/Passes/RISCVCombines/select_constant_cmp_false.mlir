// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `select` with a constant-`0` condition always picks the false operand:
// `(0 ? x : y) -> y`. The `select` is erased and its uses forwarded to `y`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%t: i64, %f: i64):
    %c = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: a constant-`1` condition is handled by the `true` rule, not
  // this one -- here it must not fold to the false operand.
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%t: i64, %f: i64):
    %c = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// The `select` is gone; the false operand is returned directly.
// CHECK:      ^{{.*}}(%{{.*}} : i64, %[[F:.*]] : i64):
// CHECK-NOT:  "llvm.select"
// CHECK:      "func.return"(%[[F]]) : (i64) -> ()

// The constant-`1` case folds to the true operand, not the false one.
// CHECK:      ^{{.*}}(%[[T:.*]] : i64, %{{.*}} : i64):
// CHECK:      "func.return"(%[[T]]) : (i64) -> ()
