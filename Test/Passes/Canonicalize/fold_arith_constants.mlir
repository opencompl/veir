// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Operations whose operands are all constants are evaluated with the
// interpreter and replaced by a constant.
"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "fold_add"}> ({
      %c7 = "arith.constant"() <{ "value" = 7 : i32 }> : () -> i32
      %c8 = "arith.constant"() <{ "value" = 8 : i32 }> : () -> i32
      %sum = "arith.addi"(%c7, %c8) : (i32, i32) -> i32
      // CHECK:      %[[C15:.*]] = "arith.constant"() <{"value" = 15 : i32}> : () -> i32
      // CHECK-NEXT: "func.return"(%[[C15]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // Folding one operation makes its users foldable in turn.
  "func.func"() <{function_type = () -> i32, sym_name = "fold_chain"}> ({
      %c1 = "arith.constant"() <{ "value" = 1 : i32 }> : () -> i32
      %c2 = "arith.constant"() <{ "value" = 2 : i32 }> : () -> i32
      %c3 = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
      %a = "arith.addi"(%c1, %c2) : (i32, i32) -> i32
      %b = "arith.muli"(%a, %c3) : (i32, i32) -> i32
      // CHECK:      %[[C9:.*]] = "arith.constant"() <{"value" = 9 : i32}> : () -> i32
      // CHECK-NEXT: "func.return"(%[[C9]]) : (i32) -> ()
      "func.return"(%b) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "arith.addi"
// CHECK-NOT: "arith.muli"
