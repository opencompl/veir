// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    ^1():
      %a = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      %b = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      %taken = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
      %nottaken = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      "riscv_cf.bge"(%a, %b, %taken, %nottaken) [^3, ^2] <{"operandSegmentSizes" = array<i64: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    ^2(%t : !riscv.reg):
      "func.return"(%t) : (!riscv.reg) -> ()
    ^3(%f : !riscv.reg):
      "func.return"(%f) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
