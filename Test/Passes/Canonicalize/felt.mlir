// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Felt operations participate in the generic interpreter-backed folder. The
// folded value is materialized back into the source dialect as `felt.const`.
"builtin.module"() ({
  // CHECK-LABEL: "sym_name" = "fold"
  "func.func"() <{function_type = () -> !felt.type<"babybear">, sym_name = "fold"}> ({
    %max = "felt.const"() <{value = #felt<const 2013265920 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %two = "felt.const"() <{value = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK-NOT: "felt.add"
    %sum = "felt.add"(%max, %two) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NOT: "felt.sub"
    %difference = "felt.sub"(%sum, %max) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NOT: "felt.mul"
    %product = "felt.mul"(%difference, %difference) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NOT: "felt.neg"
    %negated = "felt.neg"(%product) : (!felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK: %[[RESULT:.*]] = "felt.const"() <{"value" = #felt<const 2013265917 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
    // CHECK-NEXT: "func.return"(%[[RESULT]]) : (!felt.type<"babybear">) -> ()
    "func.return"(%negated) : (!felt.type<"babybear">) -> ()
  }) : () -> ()

  // Constants move to the right of commutative operations. Subtraction is
  // non-commutative, so its original operand order is retained.
  // CHECK-LABEL: "sym_name" = "commute"
  "func.func"() <{function_type = (!felt.type<"babybear">) -> !felt.type<"babybear">, sym_name = "commute"}> ({
    // CHECK: ^{{.*}}(%[[X:.*]] : !felt.type<"babybear">):
    ^bb0(%x : !felt.type<"babybear">):
      // CHECK-NEXT: %[[FIVE:.*]] = "felt.const"() <{"value" = #felt<const 5 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
      %five = "felt.const"() <{value = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
      // CHECK-NEXT: %[[SUM:.*]] = "felt.add"(%[[X]], %[[FIVE]])
      %sum = "felt.add"(%five, %x) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
      // CHECK-NEXT: %[[PRODUCT:.*]] = "felt.mul"(%[[SUM]], %[[FIVE]])
      %product = "felt.mul"(%five, %sum) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
      // CHECK-NEXT: %[[DIFFERENCE:.*]] = "felt.sub"(%[[FIVE]], %[[PRODUCT]])
      %difference = "felt.sub"(%five, %product) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
      // CHECK-NEXT: "func.return"(%[[DIFFERENCE]])
      "func.return"(%difference) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
