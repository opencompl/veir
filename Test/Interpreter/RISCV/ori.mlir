// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %b = "riscv.ori"(%a) <{ value = 3 : i12 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 29 : i64 }> : () -> i64
  %d = "riscv.ori"(%c) <{ value = -3 : i12 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000001f#64, 0xfffffffffffffffd#64]
