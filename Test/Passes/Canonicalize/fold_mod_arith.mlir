// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Folding of `mod_arith` operations. The dialect is not interpreted, so
// all-constant folds are computed in the fold table, modulo the modulus
// recovered from the result type.
"builtin.module"() ({
  // 13 + 7 = 20 = 3 (mod 17)
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "fold_add"}> ({
      %c13 = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
      %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
      %sum = "mod_arith.add"(%c13, %c7) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      // CHECK:      %[[C3:.*]] = "mod_arith.constant"() <{"value" = 3 : i32}> : () -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: "func.return"(%[[C3]]) : (!mod_arith.int<17 : i32>) -> ()
      "func.return"(%sum) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // 7 - 13 = -6 = 11 (mod 17)
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "fold_sub"}> ({
      %c13 = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
      %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
      %diff = "mod_arith.sub"(%c7, %c13) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      // CHECK:      %[[C11:.*]] = "mod_arith.constant"() <{"value" = 11 : i32}> : () -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: "func.return"(%[[C11]]) : (!mod_arith.int<17 : i32>) -> ()
      "func.return"(%diff) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // 13 * 7 = 91 = 6 (mod 17)
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "fold_mul"}> ({
      %c13 = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
      %c7 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<17 : i32>
      %prod = "mod_arith.mul"(%c13, %c7) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      // CHECK:      %[[C6:.*]] = "mod_arith.constant"() <{"value" = 6 : i32}> : () -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: "func.return"(%[[C6]]) : (!mod_arith.int<17 : i32>) -> ()
      "func.return"(%prod) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // add(x, 0) -> x; the zero is on the left, so the commutativity
  // canonicalization moves it right first.
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>, sym_name = "add_zero"}> ({
    ^bb0(%x : !mod_arith.int<17 : i32>):
      // CHECK:      ^{{.*}}(%[[X:.*]] : !mod_arith.int<17 : i32>):
      // CHECK-NEXT: "func.return"(%[[X]]) : (!mod_arith.int<17 : i32>) -> ()
      %c0 = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<17 : i32>
      %r = "mod_arith.add"(%c0, %x) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"(%r) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // mul(x, 1) -> x
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>, sym_name = "mul_one"}> ({
    ^bb0(%x : !mod_arith.int<17 : i32>):
      // CHECK:      ^{{.*}}(%[[Y:.*]] : !mod_arith.int<17 : i32>):
      // CHECK-NEXT: "func.return"(%[[Y]]) : (!mod_arith.int<17 : i32>) -> ()
      %c1 = "mod_arith.constant"() <{"value" = 1 : i32}> : () -> !mod_arith.int<17 : i32>
      %r = "mod_arith.mul"(%x, %c1) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"(%r) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // mul(x, 0) -> 0, for any x
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>, sym_name = "mul_zero"}> ({
    ^bb0(%x : !mod_arith.int<17 : i32>):
      // CHECK:      %[[C0:.*]] = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: "func.return"(%[[C0]]) : (!mod_arith.int<17 : i32>) -> ()
      %c0 = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<17 : i32>
      %r = "mod_arith.mul"(%x, %c0) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"(%r) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // sub(x, 0) -> x
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>, sym_name = "sub_zero"}> ({
    ^bb0(%x : !mod_arith.int<17 : i32>):
      // CHECK:      ^{{.*}}(%[[Z:.*]] : !mod_arith.int<17 : i32>):
      // CHECK-NEXT: "func.return"(%[[Z]]) : (!mod_arith.int<17 : i32>) -> ()
      %c0 = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<17 : i32>
      %r = "mod_arith.sub"(%x, %c0) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"(%r) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()

  // Modulus 1: every value is 0.
  "func.func"() <{function_type = () -> !mod_arith.int<1 : i32>, sym_name = "fold_mod_one"}> ({
      %c0 = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<1 : i32>
      %sum = "mod_arith.add"(%c0, %c0) : (!mod_arith.int<1 : i32>, !mod_arith.int<1 : i32>) -> !mod_arith.int<1 : i32>
      // CHECK:      %[[C0M1:.*]] = "mod_arith.constant"() <{"value" = 0 : i32}> : () -> !mod_arith.int<1 : i32>
      // CHECK-NEXT: "func.return"(%[[C0M1]]) : (!mod_arith.int<1 : i32>) -> ()
      "func.return"(%sum) : (!mod_arith.int<1 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "mod_arith.add"
// CHECK-NOT: "mod_arith.sub"
// CHECK-NOT: "mod_arith.mul"
