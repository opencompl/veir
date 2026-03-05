// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %c = "riscv.sh1adduw"(%a, %b) : (i64, i64) -> i64
  "func.return"(%c) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000006#64]
