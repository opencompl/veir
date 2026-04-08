// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 0 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 1 : i64 }> : () -> i64
  %c = "riscv.snez"(%a) : (i64) -> i64
  %d = "riscv.snez"(%b) : (i64) -> i64
  "func.return"(%c, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000001#64]
