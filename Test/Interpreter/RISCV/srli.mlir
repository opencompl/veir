// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 11 : i64 }> : () -> i64
  %b = "riscv.srli"(%a) <{ value = 3 : i6 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 11 : i64 }> : () -> i64
  %d = "riscv.srli"(%c) <{ value = -3 : i6 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
