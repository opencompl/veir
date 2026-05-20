// RUN: veir-interpret %s | filecheck %s

// In i1, -1 is also intMin, so `remsi -1, -1` is immediate UB.
"builtin.module"() ({
  %one = "arith.constant"() <{ "value" = -1 : i1 }> : () -> i1
  %y = "arith.remsi"(%one, %one) : (i1, i1) -> i1
  "func.return"(%y) : (i1) -> ()
}) : () -> ()

// CHECK: Undefined behavior
