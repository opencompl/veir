// RUN: veir-interpret %s | filecheck %s

// Check that UB is  reported together with the operation that triggered it.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %a = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %z = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %r = "arith.divsi"(%a, %z) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior at: %{{[0-9]+}} = "arith.divsi"
