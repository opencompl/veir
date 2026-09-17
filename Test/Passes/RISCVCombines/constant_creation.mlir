// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Every case checks the computed constant itself: interpreting the output alone
// would hide out-of-range attributes by truncating them back to the result width.
"builtin.module"() ({
  // Add/sub/mul share the same constant-creation site. Multiplication exercises
  // it with an overflowing result: -128 * 3 wraps to -128, not -384 : i8.
  "func.func"() <{sym_name = "fold_mul", function_type = () -> i8}> ({
    %min = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %three = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %r = "llvm.mul"(%min, %three) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Negating -128 uses the signed literal -128, rather than 128 : i8.
  "func.func"() <{sym_name = "negate_constant", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %min = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %r = "llvm.sub"(%x, %min) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Negating a product normalizes the negated multiplier in the same way.
  "func.func"() <{sym_name = "negate_product", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %min = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %product = "llvm.mul"(%x, %min) : (i8, i8) -> i8
    %r = "llvm.sub"(%zero, %product) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // Combining -128 and -127 wraps to one, rather than emitting -255 : i8.
  "func.func"() <{sym_name = "reassociate", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %min = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %max = "llvm.mlir.constant"() <{value = 127 : i8}> : () -> i8
    %inner = "llvm.add"(%x, %min) : (i8, i8) -> i8
    %r = "llvm.sub"(%inner, %max) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @fold_mul() -> i8 {
// CHECK-NEXT: %[[MUL:.*]] = "llvm.mlir.constant"() <{"value" = -128 : i8}>
// CHECK-NEXT: "func.return"(%[[MUL]]) : (i8) -> ()

// CHECK-LABEL: func.func @negate_constant
// CHECK-SAME: (%[[X:.*]]: i8) -> i8 {
// CHECK-NEXT: %[[NEG:.*]] = "llvm.mlir.constant"() <{"value" = -128 : i8}>
// CHECK-NEXT: %[[SUM:.*]] = "llvm.add"(%[[X]], %[[NEG]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[SUM]]) : (i8) -> ()

// CHECK-LABEL: func.func @negate_product
// CHECK-SAME: (%[[Y:.*]]: i8) -> i8 {
// CHECK-NEXT: %[[NEG_MUL:.*]] = "llvm.mlir.constant"() <{"value" = -128 : i8}>
// CHECK-NEXT: %[[PRODUCT:.*]] = "llvm.mul"(%[[Y]], %[[NEG_MUL]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[PRODUCT]]) : (i8) -> ()

// CHECK-LABEL: func.func @reassociate
// CHECK-SAME: (%[[Z:.*]]: i8) -> i8 {
// CHECK-NEXT: %[[COMBINED:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i8}>
// CHECK-NEXT: %[[RESULT:.*]] = "llvm.add"(%[[Z]], %[[COMBINED]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"(%[[RESULT]]) : (i8) -> ()
