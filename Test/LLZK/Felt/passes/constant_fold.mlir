// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Registered-field constants fold through the generic interpreter-backed
// canonicalizer. A nonconstant operand prevents folding.
"builtin.module"() ({
  // CHECK-LABEL: "sym_name" = "constant_fold"
  "func.func"() <{sym_name = "constant_fold", function_type = () -> !felt.type<"babybear">}> ({
    // CHECK-NOT: #felt<const 10
    %a = "felt.const"() <{value = #felt<const 10 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK-NOT: #felt<const 32
    %b = "felt.const"() <{value = #felt<const 32 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK: %[[FORTY_TWO:.*]] = "felt.const"() <{"value" = #felt<const 42 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
    %sum = "felt.add"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NEXT: "func.return"(%[[FORTY_TWO]])
    "func.return"(%sum) : (!felt.type<"babybear">) -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "mixed"
  "func.func"() <{sym_name = "mixed", function_type = (!felt.type<"babybear">) -> !felt.type<"babybear">}> ({
  ^bb0(%v : !felt.type<"babybear">):
    %five = "felt.const"() <{value = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK: "felt.add"
    %mixed = "felt.add"(%v, %five) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    "func.return"(%mixed) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
