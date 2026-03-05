// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %d = "riscv.slli"(%a) <{ value = 3 : i6 }> : (i64) -> i64
  %e = "riscv.slli"(%b) <{ value = -3 : i6 }> : (i64) -> i64
  %f = "riscv.slli"(%c) <{ value = -3 : i5 }> : (i64) -> i64
  "func.return"(%d, %e, %f) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffd8#64, 0xa000000000000000#64, 0x4000000000000000#64]