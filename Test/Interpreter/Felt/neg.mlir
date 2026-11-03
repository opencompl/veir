// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type<"babybear">}> ({
    %operand = "felt.const"() <{value = #felt<const 5 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %negated = "felt.neg"(%operand) : (!felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK: Program output: #[2013265916 : !felt.type<"babybear">]
    "func.return"(%negated) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
