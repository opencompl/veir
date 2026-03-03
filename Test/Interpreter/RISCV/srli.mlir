// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ value = 11 : i64 }> : () -> i64
  %y = "riscv.srli"(%x) <{ value = 3 : i6 }> : (i64) -> i64
  "func.return"(%y) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
