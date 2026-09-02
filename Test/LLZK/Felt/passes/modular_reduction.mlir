// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Registered fields reduce modulo their prime. Unnamed fields remain
// uninterpreted and therefore do not fold.
"builtin.module"() ({
  // CHECK-LABEL: "sym_name" = "add_reduction"
  "func.func"() <{sym_name = "add_reduction", function_type = () -> !felt.type<"babybear">}> ({
    %a = "felt.const"() <{value = #felt<const 2013265920 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %b = "felt.const"() <{value = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK: #felt<const 1 : !felt.type<"babybear">>
    %sum = "felt.add"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    "func.return"(%sum) : (!felt.type<"babybear">) -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "neg_reduction"
  "func.func"() <{sym_name = "neg_reduction", function_type = () -> !felt.type<"babybear">}> ({
    %five = "felt.const"() <{value = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK: #felt<const 2013265916 : !felt.type<"babybear">>
    %neg = "felt.neg"(%five) : (!felt.type<"babybear">) -> !felt.type<"babybear">
    "func.return"(%neg) : (!felt.type<"babybear">) -> ()
  }) : () -> ()

  // CHECK-LABEL: "sym_name" = "unnamed"
  "func.func"() <{sym_name = "unnamed", function_type = () -> !felt.type}> ({
    // CHECK-DAG: #felt<const 2013265920>
    %a = "felt.const"() <{value = #felt<const 2013265920> : !felt.type}> : () -> !felt.type
    // CHECK-DAG: #felt<const 2>
    %b = "felt.const"() <{value = #felt<const 2> : !felt.type}> : () -> !felt.type
    // CHECK: "felt.add"
    %sum = "felt.add"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NOT: #felt<const 2013265922
    "func.return"(%sum) : (!felt.type) -> ()
  }) : () -> ()
}) : () -> ()
