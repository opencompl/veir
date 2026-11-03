// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type<"babybear">}> ({
    %c = "felt.const"() <{value = #felt<const -3 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // -3 mod 2013265921 = 2013265918
    // CHECK: Program output: #[2013265918 : !felt.type<"babybear">]
    "func.return"(%c) : (!felt.type<"babybear">) -> ()
  }) : () -> ()
}) : () -> ()
