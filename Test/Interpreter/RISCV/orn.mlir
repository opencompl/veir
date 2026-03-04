// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 53 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -2 : i64 }> : () -> i64
  %d = "riscv.orn"(%a, %b) : (i64, i64) -> i64
  %e = "riscv.orn"(%a, %c) : (i64, i64) -> i64
  "func.return"(%d, %e) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffd#64, 0x0000000000000035#64]
