// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg)}> ({
    %2 = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !riscv.reg
    %4 = "riscv_stack.alloca"() <{ "value_type" = i64 }> : () -> !riscv.reg
    "riscv.sd"(%2, %4) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %6 = "riscv.ld"(%4) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%6) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000008#64]
