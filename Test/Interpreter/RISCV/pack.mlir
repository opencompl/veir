// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> i64
  %e = "riscv.pack"(%a, %b) : (i64, i64) -> i64
  %f = "riscv.pack"(%a, %c) : (i64, i64) -> i64
  %g = "riscv.pack"(%a, %d) : (i64, i64) -> i64
  "func.return"(%e, %f, %g) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000500000002#64, 0xfffffffb00000002#64, 0x0000000100000002#64]
