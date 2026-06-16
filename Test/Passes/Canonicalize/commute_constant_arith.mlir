// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A commutative `arith` op with the constant on the left: the constant is
// pushed to the right-hand side.
"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "main"}> ({
    ^bb0(%x : i32):
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
      // CHECK-NEXT: %[[C:.*]] = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
      %add = "arith.addi"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: %[[ADD:.*]] = "arith.addi"(%[[X]], %[[C]]) : (i32, i32) -> i32
      "func.return"(%add) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[ADD]]) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
