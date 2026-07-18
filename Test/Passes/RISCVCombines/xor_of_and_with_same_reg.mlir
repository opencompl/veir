// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `(x & y) ^ y` clears the bits of `y` that are set in `x` and keeps the rest,
// i.e. `(~x) & y`. It rewrites to `and (xor x, -1), y` -- an `andn`-shaped form.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "foo"}> ({
  ^bb0(%x: i64, %y: i64):
    %a = "llvm.and"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.xor"(%a, %y) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Negative case: the `xor`'s second operand is not the `and`'s operand, so no
  // fold.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64, %w: i64):
    %a = "llvm.and"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.xor"(%a, %w) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Rewritten to (x ^ -1) & y.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64):
// CHECK:      %[[M1:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i64}> : () -> i64
// CHECK-NEXT: %[[NOTX:.*]] = "llvm.xor"(%[[X]], %[[M1]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[RES:.*]] = "llvm.and"(%[[NOTX]], %[[Y]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[RES]]) : (i64) -> ()

// Unrelated `xor` operand: the original ops survive.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64, %[[NW:.*]] : i64):
// CHECK:      %[[NA:.*]] = "llvm.and"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.xor"(%[[NA]], %[[NW]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[NR]]) : (i64) -> ()
