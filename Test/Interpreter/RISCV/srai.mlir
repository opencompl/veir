// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ value = 23 : i64 }> : () -> i64
  %y = "riscv.srai"(%x) <{ value = 1 : i6 }> : (i64) -> i64
  "func.return"(%y) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000b#64]
