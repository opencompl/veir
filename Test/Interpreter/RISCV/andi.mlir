// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 23 : i64 }> : () -> i64
  %b = "riscv.andi"(%a) <{ value = 3 : i12 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 23 : i64 }> : () -> i64
  %d = "riscv.andi"(%c) <{ value = -3 : i12 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0x0000000000000015#64]
