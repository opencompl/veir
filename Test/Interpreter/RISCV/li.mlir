// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %x = "riscv.li"() <{ "value" = 3 : i64 }> : () -> !riscv.reg
    %y = "riscv.li"() <{ "value" = -2 : i64 }> : () -> !riscv.reg
    "func.return"(%x, %y) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0xfffffffffffffffe#64]

