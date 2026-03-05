// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %d = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> i64
  %e = "riscv.packh"(%a, %b) : (i64, i64) -> i64
  %f = "riscv.packh"(%a, %c) : (i64, i64) -> i64
  %g = "riscv.packh"(%a, %d) : (i64, i64) -> i64
  "func.return"(%e, %f, %g) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[#[0x0000000000000502#64, 0x000000000000fb02#64, 0x0000000000000102#64]]
