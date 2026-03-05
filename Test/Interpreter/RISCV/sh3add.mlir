// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %f = "riscv.sh3add"(%a, %b) : (i64, i64) -> i64
  %g = "riscv.sh3add"(%a, %c) : (i64, i64) -> i64
  %h = "riscv.sh3add"(%d, %a) : (i64, i64) -> i64
  "func.return"(%f, %g, %h) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000015#64, 0x000000000000000b#64, 0x0000000800000012#64]
