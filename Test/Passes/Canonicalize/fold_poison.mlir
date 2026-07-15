// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Folds that produce poison: operations that trigger immediate UB (division
// by zero), and operations whose interpreter-computed result is poison
// (overshift).
"builtin.module"() ({
  // divsi(x, 0) is immediate UB for any x: fold to poison.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "div_by_zero"}> ({
    ^bb0(%x : i32):
      // CHECK:      %[[P:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[P]]) : (i32) -> ()
      %c0 = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %r = "arith.divsi"(%x, %c0) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Fully-constant division by zero: the interpreter reports UB when
  // evaluating, and the fold produces poison.
  "func.func"() <{function_type = () -> i32, sym_name = "const_div_by_zero"}> ({
      // CHECK:      %[[P2:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[P2]]) : (i32) -> ()
      %c5 = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
      %c0 = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %r = "arith.divsi"(%c5, %c0) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // shl i64 1, 100 evaluates to poison (shift amount exceeds the bitwidth).
  "func.func"() <{function_type = () -> i64, sym_name = "overshift"}> ({
      // CHECK:      %[[P3:.*]] = "llvm.mlir.poison"() : () -> i64
      // CHECK-NEXT: "func.return"(%[[P3]]) : (i64) -> ()
      %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i64 }> : () -> i64
      %r = "llvm.shl"(%c1, %c100) : (i64, i64) -> i64
      "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Poison operands are constant-like: an all-constant operation with a
  // poison operand is evaluated and folds to poison.
  "func.func"() <{function_type = () -> i32, sym_name = "add_poison"}> ({
      // CHECK:      %[[P4:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[P4]]) : (i32) -> ()
      %p = "llvm.mlir.poison"() : () -> i32
      %c7 = "arith.constant"() <{ "value" = 7 : i32 }> : () -> i32
      %r = "arith.addi"(%p, %c7) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // Poison propagates through a chain of operations (across dialects): each
  // fold materializes a poison constant that the next fold consumes as a
  // constant-like operand, until only a single poison remains.
  "func.func"() <{function_type = () -> i32, sym_name = "poison_chain"}> ({
      // CHECK:      %[[P5:.*]] = "llvm.mlir.poison"() : () -> i32
      // CHECK-NEXT: "func.return"(%[[P5]]) : (i32) -> ()
      %p = "llvm.mlir.poison"() : () -> i32
      %c3 = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
      %a = "arith.addi"(%p, %c3) : (i32, i32) -> i32
      %b = "llvm.mul"(%a, %a) : (i32, i32) -> i32
      %r = "arith.xori"(%b, %c3) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "arith.divsi"
// CHECK-NOT: "llvm.shl"
// CHECK-NOT: "arith.addi"
// CHECK-NOT: "llvm.mul"
// CHECK-NOT: "arith.xori"
