// RUN: veir-interpret %s | filecheck %s

// A zero divisor is immediate UB, matching arith.divui.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %a = "arith.constant"() <{ "value" = 10 : i8 }> : () -> i8
    %z = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %r = "arith.ceildivui"(%a, %z) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
