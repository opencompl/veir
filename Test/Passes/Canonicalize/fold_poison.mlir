// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Operations that propagate poison fold to poison as soon as one operand is
// known to be poison, whether or not their remaining operands are constant.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "addi_poison_rhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addi_poison_rhs"
      %poison = "llvm.mlir.poison"() : () -> i32
      %sum = "arith.addi"(%x, %poison) : (i32, i32) -> i32
      // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[POISON]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // Either operand poisons the result.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "addi_poison_lhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addi_poison_lhs"
      %poison = "llvm.mlir.poison"() : () -> i32
      %sum = "arith.addi"(%poison, %x) : (i32, i32) -> i32
      // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[POISON]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // The poison constant takes the result's own type, not the operands'.
  "func.func"() <{function_type = (i32) -> i1, sym_name = "cmpi_poison"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "cmpi_poison"
      %poison = "llvm.mlir.poison"() : () -> i32
      %cmp = "arith.cmpi"(%x, %poison) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
      // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i1
      // CHECK-NEXT: "func.return"(%[[POISON]]) : (i1) -> ()
      "func.return"(%cmp) : (i1) -> ()
  }) : () -> ()

  // Both results of a multiple-result operation are poisoned, even though only
  // one operand is known.
  "func.func"() <{function_type = (i8) -> (i8, i1), sym_name = "extended_add_poison"}> ({
    ^bb0(%x : i8):
      // CHECK-LABEL: "sym_name" = "extended_add_poison"
      %poison = "llvm.mlir.poison"() : () -> i8
      %sum, %overflow = "arith.addui_extended"(%x, %poison) : (i8, i8) -> (i8, i1)
      // CHECK: %[[SUM:.*]] = "llvm.mlir.poison"() : () -> i8
      // CHECK-NEXT: %[[FLAG:.*]] = "llvm.mlir.poison"() : () -> i1
      // CHECK-NEXT: "func.return"(%[[SUM]], %[[FLAG]]) : (i8, i1) -> ()
      "func.return"(%sum, %overflow) : (i8, i1) -> ()
  }) : () -> ()

  // The same holds for the `llvm` dialect.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "llvm_add_poison"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "llvm_add_poison"
      %poison = "llvm.mlir.poison"() : () -> i32
      %sum = "llvm.add"(%x, %poison) : (i32, i32) -> i32
      // CHECK: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[POISON]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // `arith.select` does not propagate poison: the poisoned arm may be the one
  // that the unknown condition does not select.
  "func.func"() <{function_type = (i1, i32) -> i32, sym_name = "select_poison_arm"}> ({
    ^bb0(%cond : i1, %x : i32):
      // CHECK-LABEL: "sym_name" = "select_poison_arm"
      // CHECK:      ^{{.*}}(%[[COND:.*]] : i1, %[[X:.*]] : i32):
      %poison = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: %[[POISON:.*]] = "llvm.mlir.poison"() : () -> i32
      %sel = "arith.select"(%cond, %x, %poison) : (i1, i32, i32) -> i32
      // CHECK-NEXT: %[[SEL:.*]] = "arith.select"(%[[COND]], %[[X]], %[[POISON]]) : (i1, i32, i32) -> i32
      "func.return"(%sel) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[SEL]]) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "arith.addi"
// CHECK-NOT: "arith.cmpi"
// CHECK-NOT: "arith.addui_extended"
// CHECK-NOT: "llvm.add"
