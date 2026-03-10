// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "arith.constant"() <{ "value" = 23 : i10 }> : () -> i10
  %q = "arith.constant"() <{ "value" = 17 : i10 }> : () -> i10
  %r = "mod_arith.subifge"(%x, %q) : (i10, i10) -> i10
  "func.return"(%r) : (i10) -> ()
}) : () -> ()

// CHECK: Program output: #[0x006#10]
