// RUN: not veir-interpret %s 2>&1 | filecheck %s

// Check that an error is reported together with the operation that triggered it.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %a = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %r = "test.unknown"(%a) : (i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error while interpreting module at: %{{[0-9]+}} = "test.unknown"
