// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 3 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.slt"(%a, %b) : (i64, i64) -> i64
  %e = "riscv.slt"(%a, %c) : (i64, i64) -> i64
  "func.return"(%d, %e) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
