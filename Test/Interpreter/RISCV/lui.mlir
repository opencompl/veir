// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.lui"() <{ value = -5 : i20 }> : () -> i64
  %y = "riscv.lui"() <{ value = 3 : i20 }> : () -> i64
  "func.return"(%x, %y) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffd000#64, 0x0000000000003000#64]
