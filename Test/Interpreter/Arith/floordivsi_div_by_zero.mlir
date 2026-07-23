// RUN: veir-interpret %s | filecheck %s

// A zero divisor is immediate UB, matching arith.divsi.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %a = "arith.constant"() <{ "value" = 7 : i8 }> : () -> i8
    %z = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %r = "arith.floordivsi"(%a, %z) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
