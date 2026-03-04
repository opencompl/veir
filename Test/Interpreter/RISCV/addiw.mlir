// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.addiw"(%a) <{ value = 3 : i12 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %d = "riscv.addiw"(%c) <{ value = -31 : i12 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64, 0xffffffffffffffe3#64]
