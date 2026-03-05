// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %e = "riscv.li"() <{ value = -3 : i64 }> : () -> i64
  %f = "riscv.mulh"(%a, %b) : (i64, i64) -> i64
  %g = "riscv.mulh"(%a, %c) : (i64, i64) -> i64
  %h = "riscv.mulh"(%d, %e) : (i64, i64) -> i64
  "func.return"(%f, %g, %h) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0xffffffffffffffff#64, 0xffffffffffffffff#64]
