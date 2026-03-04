// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.sltiu"(%a) <{ value = 33 : i12 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %d = "riscv.sltiu"(%c) <{ value = -33 : i12 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000001#64]
