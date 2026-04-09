// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 0 : i64 }> : () -> i64
  %b = "riscv.li"() <{ value = 1 : i64 }> : () -> i64
  %c = "riscv.li"() <{ value = -1 : i64 }> : () -> i64
  %d = "riscv.sltz"(%a) : (i64) -> i64
  %e = "riscv.sltz"(%b) : (i64) -> i64
  %f = "riscv.sltz"(%c) : (i64) -> i64
  "func.return"(%d, %e, %f) : (i64, i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000000#64, 0x0000000000000001#64]
