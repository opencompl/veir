// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `trunc (sub X, C)` is `sub (trunc X, trunc C)`: a sub's low bits depend only on
// its inputs' low bits, so the truncation can be pushed onto each operand and the
// sub redone at the narrow width. The constant operand must be second.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %sub = "llvm.sub"(%x, %c) : (i64, i64) -> i64
    %r = "llvm.trunc"(%sub) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the second operand is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i64, i64) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %sub = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.trunc"(%sub) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The sub runs on the narrowed operands.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[TX:.*]] = "llvm.trunc"(%[[X]]) : (i64) -> i32
// CHECK:      %[[TC:.*]] = "llvm.trunc"(%{{.*}}) : (i64) -> i32
// CHECK:      %[[R:.*]] = "llvm.sub"(%[[TX]], %[[TC]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-constant second operand: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NSUB:.*]] = "llvm.sub"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.trunc"(%[[NSUB]]) : (i64) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
