// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = -2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 3 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -3 : i64 }> : () -> i64
  %d = "riscv.sra"(%a, %b) : (i64, i64) -> i64
  %e = "riscv.sra"(%a, %c) : (i64, i64) -> i64
  "func.return"(%d, %e) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffff#64, 0xffffffffffffffff#64]
