// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ "value" = 0 : i64 }> : () -> i64
  %y = "riscv.lui"(%x) <{ "value" = 3 : i20 }> : (i64) -> i64
  "func.return"(%y) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64]
