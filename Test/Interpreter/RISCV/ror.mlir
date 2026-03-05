// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %e = "riscv.ror"(%a, %b) : (i64, i64) -> i64
  %f = "riscv.ror"(%a, %d) : (i64, i64) -> i64
  %g = "riscv.ror"(%c, %b) : (i64, i64) -> i64
  "func.return"(%e, %f, %g) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x1000000000000000#64, 0x0000000000000040#64, 0x1000000008000000#64]
