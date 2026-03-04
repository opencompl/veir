// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ value = 53 : i64 }> : () -> i64
  %y = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %z = "riscv.srl"(%x, %y) : (i64, i64) -> i64
  "func.return"(%z) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000d#64]
