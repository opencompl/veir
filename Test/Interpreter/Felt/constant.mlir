// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type<"babybear">}> ({
    %c = "felt.const"() <{value = #felt<const 42 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK: Program output: #[42 : !felt.type<"babybear">]
    "func.return"(%c) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
