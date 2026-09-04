// RUN: not veir-interpret %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "main", function_type = () -> ()}> ({
    %lhs = "felt.const"() <{value = #felt<const 1 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %rhs = "felt.const"() <{value = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK: Error while interpreting module
    "constrain.eq"(%lhs, %rhs) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint} : () -> ()
}) : () -> ()
