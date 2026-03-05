// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 4294967296 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 3 : i64 }> : () -> i64
  %c = "riscv.divuw"(%a, %b) : (i64, i64) -> i64
  "func.return"(%c) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
