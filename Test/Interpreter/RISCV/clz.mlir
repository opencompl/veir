// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> i64
  %d = "riscv.clz"(%a) : (i64) -> i64
  %e = "riscv.clz"(%b) : (i64) -> i64
  %f = "riscv.clz"(%c) : (i64) -> i64
  "func.return"(%d, %e, %f) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000003e#64, 0x0000000000000000#64, 0x000000000000001f#64]
