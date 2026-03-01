// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %y = "riscv.lui"() <{ value = 3 : i20 }> : () -> i64
  "func.return"(%y) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000003000#64]
