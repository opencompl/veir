// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %b = "riscv.slliw"(%a) <{ value = 3 : i5 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %d = "riscv.slliw"(%c) <{ value = -3 : i5 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000e8#64, 0xffffffffa0000000#64]
