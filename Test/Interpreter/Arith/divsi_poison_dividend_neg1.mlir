// RUN: veir-interpret %s | filecheck %s

// `divsi poison, -1` (width > 1) is immediate UB: the poison dividend could
// refine to intMin, in which case the overflow case applies.
"builtin.module"() ({
  %neg1 = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "arith.constant"() <{ "value" = 1 : i32 }> : () -> i32
  %poison = "arith.addi"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "arith.divsi"(%poison, %neg1) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
