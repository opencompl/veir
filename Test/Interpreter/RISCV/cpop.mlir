// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %d = "riscv.cpop"(%a) : (i64) -> i64
  %e = "riscv.cpop"(%b) : (i64) -> i64
  %f = "riscv.cpop"(%c) : (i64) -> i64
  "func.return"(%d, %e, %f) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x000000000000003f#64, 0x0000000000000002#64]
