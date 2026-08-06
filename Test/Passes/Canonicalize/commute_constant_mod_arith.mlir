// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Commutative `mod_arith` ops with the constant on the left: the constant is
// pushed to the right-hand side. `mod_arith.sub` is not commutative and is
// left alone, which also confirms the reordering keys off `isCommutative`
// rather than firing on every `mod_arith` op with a constant operand.
"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>) -> (), sym_name = "main"}> ({
    ^bb0(%x : !mod_arith.int<17 : i32>):
      // CHECK:      ^{{.*}}(%[[X:.*]] : !mod_arith.int<17 : i32>):
      %c = "mod_arith.constant"() <{"value" = 5 : i32}> : () -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: %[[C:.*]] = "mod_arith.constant"() <{"value" = 5 : i32}> : () -> !mod_arith.int<17 : i32>

      %add = "mod_arith.add"(%c, %x)
        : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: %[[ADD:.*]] = "mod_arith.add"(%[[X]], %[[C]])

      %mul = "mod_arith.mul"(%c, %x)
        : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: %[[MUL:.*]] = "mod_arith.mul"(%[[X]], %[[C]])

      // Not commutative: the operand order is preserved.
      %sub = "mod_arith.sub"(%c, %x)
        : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      // CHECK-NEXT: %[[SUB:.*]] = "mod_arith.sub"(%[[C]], %[[X]])

      "test.test"(%add, %mul, %sub)
        : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>,
           !mod_arith.int<17 : i32>) -> ()
      // CHECK-NEXT: "test.test"(%[[ADD]], %[[MUL]], %[[SUB]])
      "func.return"() : () -> ()
      // CHECK-NEXT: "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
