// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %x = "riscv.li"() <{ "value" = 3 : i64 }> : () -> !reg
  %u = "builtin.unrealized_conversion_cast"(%x) : (!reg) -> i8
  %v = "builtin.unrealized_conversion_cast"(%u) : (i8) -> !reg
  "func.return"(%u, %v) : (i8, !reg) -> ()
}) : () -> ()

// CHECK: Program output: #[0x03#8, 0x0000000000000003#64]

