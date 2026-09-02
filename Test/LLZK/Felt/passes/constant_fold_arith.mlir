// RUN: veir-opt %s -p=canonicalize | filecheck %s

// The generic canonicalizer folds registered-field subtraction,
// multiplication, and negation.
"builtin.module"() ({
  // CHECK-LABEL: "sym_name" = "constant_fold_arith"
  "func.func"() <{sym_name = "constant_fold_arith", function_type = () -> (!felt.type<"babybear">, !felt.type<"babybear">, !felt.type<"babybear">)}> ({
    %a = "felt.const"() <{value = #felt<const 7 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %b = "felt.const"() <{value = #felt<const 3 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK-DAG: "felt.const"() <{"value" = #felt<const 4 : !felt.type<"babybear">>}>
    %d = "felt.sub"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-DAG: "felt.const"() <{"value" = #felt<const 21 : !felt.type<"babybear">>}>
    %p = "felt.mul"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-DAG: "felt.const"() <{"value" = #felt<const 2013265914 : !felt.type<"babybear">>}>
    %n = "felt.neg"(%a) : (!felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NOT: "felt.sub"
    // CHECK-NOT: "felt.mul"
    // CHECK-NOT: "felt.neg"
    "func.return"(%d, %p, %n) : (!felt.type<"babybear">, !felt.type<"babybear">, !felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
