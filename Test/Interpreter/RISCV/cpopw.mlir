// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
  %c = "riscv.cpopw"(%a) : (i64) -> i64
  %d = "riscv.cpopw"(%b) : (i64) -> i64
  "func.return"(%c, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x000000000000001f#64]
