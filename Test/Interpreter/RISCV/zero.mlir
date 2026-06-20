// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %a = "rv64.get_register"() : () -> !riscv.reg<x0>
    %b = "riscv.addi"(%a) <{ value = 5 : i12 }> : (!riscv.reg<x0>) -> !riscv.reg
    "func.return"(%b) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64]
