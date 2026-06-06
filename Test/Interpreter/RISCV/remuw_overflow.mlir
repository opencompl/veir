// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = -3 : i64 }> : () -> !riscv.reg
    %c = "riscv.remuw"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%c) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64]
