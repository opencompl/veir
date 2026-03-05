// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %c = "riscv.ctzw"(%a) : (i64) -> i64
  %d = "riscv.ctzw"(%b) : (i64) -> i64
  "func.return"(%c, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
