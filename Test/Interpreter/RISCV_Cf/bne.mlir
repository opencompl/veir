// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^1():
      %x1 = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
      %x2 = "riscv.li"() <{"value" = 11 : i64}> : () -> !riscv.reg
      "riscv_cf.bne"(%x1, %x2, %x2, %x1) [^3, ^4] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    ^4(%a1 : !riscv.reg):
      %a2 = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      "func.return"(%a2) : (!riscv.reg) -> ()
    ^3(%z1 : !riscv.reg):
      %z2 = "riscv.li"() <{"value" = 11 : i64}> : () -> !riscv.reg
      "riscv_cf.bne"(%z1, %z2, %z2, %z1) [^4, ^2] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    ^2(%y : !riscv.reg):
      "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000b#64]
