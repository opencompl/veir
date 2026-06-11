// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 7 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 7 : i64 }> : () -> !riscv.reg
    %d = "riscv.xnor"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %e = "riscv.xnor"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%d, %e) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffd#64, 0xfffffffffffffffd#64]
