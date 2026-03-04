// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 23 : i64 }> : () -> i64
  %b = "riscv.sraiw"(%a) <{ value = 1 : i6 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 23 : i64 }> : () -> i64
  %d = "riscv.sraiw"(%c) <{ value = -1 : i6 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000b#64, 0x0000000000000000#64]
