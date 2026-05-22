// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^1():
      %x1 = "riscv.li"() <{"value" = 8 : i64}> : () -> i64
      %x2 = "riscv.li"() <{"value" = 11 : i64}> : () -> i64
      "riscv_cf.bne"(%x1, %x2, %x2, %x1) [^3, ^4] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (i64, i64, i64, i64) -> ()
    ^4(%a1 : i64):
      %a2 = "riscv.li"() <{"value" = 5 : i64}> : () -> i64
      "func.return"(%a2) : (i64) -> ()
    ^3(%z1 : i64):
      %z2 = "riscv.li"() <{"value" = 11 : i64}> : () -> i64
      "riscv_cf.bne"(%z1, %z2, %z2, %z1) [^4, ^2] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (i64, i64, i64, i64) -> ()
    ^2(%y : i64):
      "func.return"(%y) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000b#64]
