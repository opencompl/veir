// RUN: veir-interpret %s | filecheck %s

// `remsi poison, -1` (width > 1) is immediate UB: the poison dividend could
// refine to intMin, hitting the overflow case.
"builtin.module"() ({
  %neg1 = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "arith.constant"() <{ "value" = 1 : i32 }> : () -> i32
  %poison = "arith.addi"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "arith.remsi"(%poison, %neg1) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
