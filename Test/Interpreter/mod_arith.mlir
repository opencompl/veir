// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "mod_arith.constant"() <{ "value" = 5 : i32 }> : () -> !mod_arith.int<17 : i32>
  %b = "mod_arith.constant"() <{ "value" = 9 : i32 }> : () -> !mod_arith.int<17 : i32>
  %c = "mod_arith.constant"() <{ "value" = 4 : i32 }> : () -> !mod_arith.int<17 : i32>
  %s1 = "mod_arith.add"(%a, %b) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
  %p1 = "mod_arith.mul"(%s1, %c) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
  %s2 = "mod_arith.add"(%p1, %b) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
  %p2 = "mod_arith.mul"(%s2, %a) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
  %out = "mod_arith.extract"(%p2) : (!mod_arith.int<17 : i32>) -> i32
  "func.return"(%out) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000002#32]
