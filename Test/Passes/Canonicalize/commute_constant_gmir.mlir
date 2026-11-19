// RUN: veir-opt %s -p=canonicalize | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i32) -> i32, sym_name = "main"}> ({
    ^bb0(%x : i32):
      // CHECK:      func.func @main(%[[X:.*]]: i32) -> i32 {
      %c = "gmir.g_constant"() <{ "value" = 5 : i32 }> : () -> i32
      // CHECK-NEXT: %[[C:.*]] = "gmir.g_constant"() <{"value" = 5 : i32}> : () -> i32

      // Commutative op with the constant on the left: operands are swapped
      // so the constant is pushed to the right.
      %add = "gmir.g_add"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: %[[ADD:.*]] = "gmir.g_add"(%[[X]], %[[C]]) : (i32, i32) -> i32

      // The high half of a multiply is commutative, signed and unsigned.
      %smulh = "gmir.g_smulh"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: %[[SMULH:.*]] = "gmir.g_smulh"(%[[X]], %[[C]]) : (i32, i32) -> i32
      %umulh = "gmir.g_umulh"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: %[[UMULH:.*]] = "gmir.g_umulh"(%[[X]], %[[C]]) : (i32, i32) -> i32

      // Non-commutative op: operands are left untouched.
      %sub = "gmir.g_sub"(%c, %x) : (i32, i32) -> i32
      // CHECK-NEXT: "gmir.g_sub"(%[[C]], %[[X]]) : (i32, i32) -> i32

      "test.test"(%add, %smulh, %umulh, %sub) : (i32, i32, i32, i32) -> ()
      "func.return"(%add) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
