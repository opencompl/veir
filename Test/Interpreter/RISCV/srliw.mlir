// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %b = "riscv.srliw"(%a) <{ value = 3 : i5 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %d = "riscv.srliw"(%c) <{ value = -3 : i5 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0x0000000000000000#64]
