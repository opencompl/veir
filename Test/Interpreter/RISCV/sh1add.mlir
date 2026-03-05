// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %f = "riscv.sh1add"(%a, %b) : (i64, i64) -> i64
  %g = "riscv.sh1add"(%a, %c) : (i64, i64) -> i64
  %h = "riscv.sh1add"(%d, %a) : (i64, i64) -> i64
  "func.return"(%f, %g, %h) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64, 0xffffffffffffffff#64, 0x0000000200000006#64]
