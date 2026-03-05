// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %d = "riscv.roriw"(%a) <{ value = 3 : i6 }> : (i64) -> i64
  %e = "riscv.roriw"(%b) <{ value = -3 : i6 }> : (i64) -> i64
  %f = "riscv.roriw"(%c) <{ value = -3 : i6 }> : (i64) -> i64
  "func.return"(%d, %e, %f) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffa0000003#64, 0x00000000000000e8#64, 0x0000000000000010#64]
