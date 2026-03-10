// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "arith.constant"() <{ "value" = 23 : i10 }> : () -> i10
  %mx = "mod_arith.encapsulate"(%x) : (i10) -> !mod_arith.int<17 : i10>
  %r = "mod_arith.reduce"(%mx) : (!mod_arith.int<17 : i10>) -> !mod_arith.int<17 : i10>
  %out = "mod_arith.extract"(%r) : (!mod_arith.int<17 : i10>) -> i10
  "func.return"(%out) : (i10) -> ()
}) : () -> ()

// CHECK: Program output: #[0x006#10]
