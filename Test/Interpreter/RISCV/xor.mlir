// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %y = "riscv.li"() <{ value = 7 : i64 }> : () -> i64
  %z = "riscv.xor"(%x, %y) : (i64, i64) -> i64
  "func.return"(%z) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64]
