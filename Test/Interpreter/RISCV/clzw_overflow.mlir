// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> i64
  %b = "riscv.clzw"(%a) : (i64) -> i64
  "func.return"(%b) : (i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000001f#64]
