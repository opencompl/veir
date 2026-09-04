// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type<"babybear">}> ({
    %lhs = "felt.const"() <{value = #felt<const 3 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %rhs = "felt.const"() <{value = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %difference = "felt.sub"(%lhs, %rhs) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK: Program output: #[2013265919 : !felt.type<"babybear">]
    "func.return"(%difference) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
