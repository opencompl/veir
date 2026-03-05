// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %b = "riscv.slliuw"(%a) <{ value = -3 : i5 }> : (i64) -> i64
  "func.return"(%b) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x4000000000000000#64]
