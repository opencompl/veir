// RUN: not veir-interpret %s 2>&1 | filecheck %s
// TODO: also run with `--ctree` once it reports source locations.

// CHECK:      error: failed to interpret operation
// CHECK-NEXT:     %c = "felt.const"() <{value = #felt<const 42> : !felt.type}> : () -> !felt.type
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !felt.type}> ({
    %c = "felt.const"() <{value = #felt<const 42> : !felt.type}> : () -> !felt.type
    "func.return"(%c) : (!felt.type) -> ()
  }) : () -> ()
}) : () -> ()
