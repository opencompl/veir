// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 7 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = 7 : i64 }> : () -> i64
  %d = "riscv.xnor"(%a, %b) : (i64, i64) -> i64
  %e = "riscv.xnor"(%a, %c) : (i64, i64) -> i64
  "func.return"(%d, %e) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffd#64, 0xfffffffffffffffd#64]
