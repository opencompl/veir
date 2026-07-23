// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Select with a known condition folds to the selected operand.
"builtin.module"() ({
  // select(true, x, y) -> x
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "select_true"}> ({
    ^bb0(%x : i32, %y : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32, %{{.*}} : i32):
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      %true = "arith.constant"() <{ "value" = 1 : i1 }> : () -> i1
      %r = "arith.select"(%true, %x, %y) : (i1, i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // select(false, x, y) -> y
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "select_false"}> ({
    ^bb0(%x : i32, %y : i32):
      // CHECK:      ^{{.*}}(%{{.*}} : i32, %[[Y:.*]] : i32):
      // CHECK-NEXT: "func.return"(%[[Y]]) : (i32) -> ()
      %false = "arith.constant"() <{ "value" = 0 : i1 }> : () -> i1
      %r = "arith.select"(%false, %x, %y) : (i1, i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // llvm.select(true, x, y) -> x
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "llvm_select_true"}> ({
    ^bb0(%x : i32, %y : i32):
      // CHECK:      ^{{.*}}(%[[X2:.*]] : i32, %{{.*}} : i32):
      // CHECK-NEXT: "func.return"(%[[X2]]) : (i32) -> ()
      %true = "llvm.mlir.constant"() <{ "value" = 1 : i1 }> : () -> i1
      %r = "llvm.select"(%true, %x, %y) : (i1, i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // llvm.select(false, x, y) -> y
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "llvm_select_false"}> ({
    ^bb0(%x : i32, %y : i32):
      // CHECK:      ^{{.*}}(%{{.*}} : i32, %[[Y2:.*]] : i32):
      // CHECK-NEXT: "func.return"(%[[Y2]]) : (i32) -> ()
      %false = "llvm.mlir.constant"() <{ "value" = 0 : i1 }> : () -> i1
      %r = "llvm.select"(%false, %x, %y) : (i1, i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // select with a poison condition must NOT fold to an operand: the result is
  // poison, which neither operand refines in general. (It is also not folded
  // to a poison constant by the current table.)
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "select_poison_cond"}> ({
    ^bb0(%x : i32, %y : i32):
      // CHECK:      "llvm.select"
      %p = "llvm.mlir.poison"() : () -> i1
      %r = "llvm.select"(%p, %x, %y) : (i1, i32, i32) -> i32
      "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "arith.select"
