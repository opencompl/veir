// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `trunc (add X, C)` is `add (trunc X, trunc C)`: an add's low bits depend only
// on its inputs' low bits, so the truncation can be pushed onto each operand and
// the add redone at the narrow width. The constant operand must be second.

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i64):
    %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %add = "llvm.add"(%x, %c) : (i64, i64) -> i64
    %r = "llvm.trunc"(%add) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negative case: the second operand is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i64, i64) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i64, %y: i64):
    %add = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.trunc"(%add) : (i64) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The add runs on the narrowed operands.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64):
// CHECK:      %[[TX:.*]] = "llvm.trunc"(%[[X]]) : (i64) -> i32
// CHECK:      %[[TC:.*]] = "llvm.trunc"(%{{.*}}) : (i64) -> i32
// CHECK:      %[[R:.*]] = "llvm.add"(%[[TX]], %[[TC]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Non-constant second operand: the pattern does not fire.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i64, %[[NY:.*]] : i64):
// CHECK:      %[[NADD:.*]] = "llvm.add"(%[[NX]], %[[NY]]) : (i64, i64) -> i64
// CHECK:      %[[NR:.*]] = "llvm.trunc"(%[[NADD]]) : (i64) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
