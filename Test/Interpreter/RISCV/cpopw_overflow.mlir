// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> i64
  %b = "riscv.cpopw"(%a) : (i64) -> i64
  "func.return"(%b) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
