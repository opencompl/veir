// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "arith.constant"() <{ "value" = 23 : i10 }> : () -> i10
  %r = "mod_arith.barrett_reduce"(%x) <{ "modulus" = 17 : i64 }> : (i10) -> i10
  "func.return"(%r) : (i10) -> ()
}) : () -> ()

// CHECK: Program output: #[0x006#10]
