// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ "value" = 3 : i64 }> : () -> i64
  %y = "riscv.li"() <{ "value" = -2 : i64 }> : () -> i64
  "func.return"(%x, %y) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0xfffffffffffffffe#64]

