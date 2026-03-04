// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %c = "riscv.bclri"(%a) <{ value = 2 : i12 }> : (i64) -> i64
  %d = "riscv.bclri"(%b) <{ value = 5 : i12 }> : (i64) -> i64
  "func.return"(%c, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64, 0xffffffffffffffdb#64]
