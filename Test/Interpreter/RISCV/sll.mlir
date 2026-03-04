// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ value = 21 : i64 }> : () -> i64
  %y = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %z = "riscv.sll"(%x, %y) : (i64, i64) -> i64
  "func.return"(%z) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000002a0#64]
