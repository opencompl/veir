// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %y = "riscv.slli"(%x) <{ value = 3 : i6 }> : (i64) -> i64
  "func.return"(%y) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000e8#64]
