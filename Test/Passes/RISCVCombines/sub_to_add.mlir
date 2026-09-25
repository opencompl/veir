// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `sub x, C` is `add x, -C` when the second operand is a constant.

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "foo"}> ({
  ^bb0(%x: i32):
    %c = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %r = "llvm.sub"(%x, %c) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Negating the signed minimum must wrap back to the normalized i8 value.
  "func.func"() <{function_type = (i8) -> i8, sym_name = "sub_to_add_min"}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %c) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Negative case: the second operand is not a constant, so the pattern does not fire.
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "bar"}> ({
  ^bb0(%x: i32, %y: i32):
    %r = "llvm.sub"(%x, %y) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// The sub becomes an add against the negated constant.
// CHECK:      func.func @foo(%[[X:.*]]: i32) -> i32 {
// CHECK:      %[[NC:.*]] = "llvm.mlir.constant"() <{"value" = -7 : i32}> : () -> i32
// CHECK:      %[[R:.*]] = "llvm.add"(%[[X]], %[[NC]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[R]]) : (i32) -> ()

// Check the rewritten add and its use, not just the constant already in the input.
// CHECK-LABEL: func.func @sub_to_add_min(%[[MIN_X:.*]]: i8) -> i8 {
// CHECK: %[[MIN_C:.*]] = "llvm.mlir.constant"() <{"value" = -128 : i8}> : () -> i8
// CHECK-NEXT: %[[MIN_SUM:.*]] = "llvm.add"(%[[MIN_X]], %[[MIN_C]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[MIN_SUM]]) : (i8) -> ()

// Non-constant second operand: the sub remains.
// CHECK:      func.func @bar(%[[NX:.*]]: i32, %[[NY:.*]]: i32) -> i32 {
// CHECK:      %[[NR:.*]] = "llvm.sub"(%[[NX]], %[[NY]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[NR]]) : (i32) -> ()
