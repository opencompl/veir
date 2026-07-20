// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `trunc (mul X, C)` is `mul (trunc X, trunc C)`: a mul's low bits depend only on
// its inputs' low bits, so the truncation can be pushed onto each operand and the
// mul redone at the narrow width. The constant operand must be second.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %mul = "llvm.mul"(%x, %c) : (i64, i64) -> i64
    %r = "llvm.trunc"(%mul) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the second operand is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i64, i64) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %mul = "llvm.mul"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.trunc"(%mul) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The mul runs on the narrowed operands.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[TX:.*]] = "llvm.trunc"(%[[X]]) : (i64) -> i32
// CHECK:      %[[TC:.*]] = "llvm.trunc"(%{{.*}}) : (i64) -> i32
// CHECK:      %[[R:.*]] = "llvm.mul"(%[[TX]], %[[TC]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-constant second operand: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NMUL:.*]] = "llvm.mul"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.trunc"(%[[NMUL]]) : (i64) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
