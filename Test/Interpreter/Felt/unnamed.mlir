// RUN: not veir-interpret %s 2>&1 | filecheck %s

// CHECK: Error while interpreting module
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type}> ({
    %c = "felt.const"() <{value = #felt<const 42> : !felt.type}> : () -> !felt.type
    "func.return"(%c) : (!felt.type) -> ()
  }) : () -> ()
}) : () -> ()
