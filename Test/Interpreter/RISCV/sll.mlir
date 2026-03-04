// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 21 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.sll"(%a, %b) : (i64, i64) -> i64
  %e = "riscv.sll"(%a, %c) : (i64, i64) -> i64
  "func.return"(%d, %e) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000002a0#64, 0xa800000000000000#64]
