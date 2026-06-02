// RUN: veir-interpret %s | filecheck %s

// In i1, -1 is also intMin, so `divsi -1, -1` is immediate UB.
"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %one = "arith.constant"() <{ "value" = -1 : i1 }> : () -> i1
    %y = "arith.divsi"(%one, %one) : (i1, i1) -> i1
    "func.return"(%y) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
