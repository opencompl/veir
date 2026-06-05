// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 23 : i64 }> : () -> !riscv.reg
    %b = "riscv.andi"(%a) <{ value = 3 : i12 }> : (!riscv.reg) -> !riscv.reg
    %c = "riscv.li"() <{ value = 23 : i64 }> : () -> !riscv.reg
    %d = "riscv.andi"(%c) <{ value = -3 : i12 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b, %d) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0x0000000000000015#64]
