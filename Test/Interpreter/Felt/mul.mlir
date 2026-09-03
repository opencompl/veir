// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type<"babybear">}> ({
    %lhs = "felt.const"() <{value = #felt<const 2013265920 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %rhs = "felt.const"() <{value = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %product = "felt.mul"(%lhs, %rhs) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK: Program output: #[2013265919 : !felt.type<"babybear">]
    "func.return"(%product) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
