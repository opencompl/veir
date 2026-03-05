// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.adduw"(%a, %b) : (i64, i64) -> i64
  "func.return"(%c) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000006#64]
