// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 5 : i64 }> : () -> i64
  %b = "riscv.neg"(%a) : (i64) -> i64
  "func.return"(%b) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffb#64]
