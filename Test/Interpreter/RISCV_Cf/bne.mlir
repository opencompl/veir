// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^1():
      %x1 = "riscv.li"() <{"value" = 8 : i64}> : () -> !reg
      %x2 = "riscv.li"() <{"value" = 11 : i64}> : () -> !reg
      "riscv_cf.bne"(%x1, %x2, %x2, %x1) [^3, ^4] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (!reg, !reg, !reg, !reg) -> ()
    ^4(%a1 : !reg):
      %a2 = "riscv.li"() <{"value" = 5 : i64}> : () -> !reg
      "func.return"(%a2) : (!reg) -> ()
    ^3(%z1 : !reg):
      %z2 = "riscv.li"() <{"value" = 11 : i64}> : () -> !reg
      "riscv_cf.bne"(%z1, %z2, %z2, %z1) [^4, ^2] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (!reg, !reg, !reg, !reg) -> ()
    ^2(%y : !reg):
      "func.return"(%y) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000b#64]
