// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %a = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %b = "riscv.auipc"(%a) <{ value = 3 : i20 }> : (i64) -> i64
  %c = "riscv.li"() <{ value = 2 : i64 }> : () -> i64
  %d = "riscv.auipc"(%c) <{ value = -3 : i20 }> : (i64) -> i64
  "func.return"(%b, %d) : (i64, i64) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000003002#64, 0xffffffffffffd002#64]
