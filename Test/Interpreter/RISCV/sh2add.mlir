// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %f = "riscv.sh2add"(%a, %b) : (i64, i64) -> i64
  %g = "riscv.sh2add"(%a, %c) : (i64, i64) -> i64
  %h = "riscv.sh2add"(%d, %a) : (i64, i64) -> i64
  "func.return"(%f, %g, %h) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000d#64, 0x0000000000000003#64, 0x000000040000000a#64]
