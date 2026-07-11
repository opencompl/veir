// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Identity folds: the fold table reports that the result of the operation is
// one of its operands (or a known constant), even though not all operands are
// constant.
"builtin.module"() ({
  // addi(x, 0) -> x
  "func.func"() <{function_type = (i32) -> i32, sym_name = "add_zero"}> ({
    ^bb0(%x : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      %c0 = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %r = "arith.addi"(%x, %c0) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // addi(0, x) -> x: the constant is first moved to the right by the
  // commutativity canonicalization, then the identity fold applies.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "add_zero_lhs"}> ({
    ^bb0(%x : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      %c0 = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %r = "arith.addi"(%c0, %x) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // muli(x, 1) -> x
  "func.func"() <{function_type = (i32) -> i32, sym_name = "mul_one"}> ({
    ^bb0(%x : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      %c1 = "arith.constant"() <{ "value" = 1 : i32 }> : () -> i32
      %r = "arith.muli"(%x, %c1) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // muli(x, 0) -> 0, for any x
  "func.func"() <{function_type = (i32) -> i32, sym_name = "mul_zero"}> ({
    ^bb0(%x : i32):
      // CHECK:      %[[C0:.*]] = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
      // CHECK-NEXT: "func.return"(%[[C0]]) : (i32) -> ()
      %c0 = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
      %r = "arith.muli"(%x, %c0) : (i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "arith.addi"
// CHECK-NOT: "arith.muli"
