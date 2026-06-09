// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 0 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 256 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -1 : i64 }> : () -> !riscv.reg
    %d = "riscv.orcb"(%a) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.orcb"(%b) : (!riscv.reg) -> !riscv.reg
    %f = "riscv.orcb"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%d, %e, %f) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x000000000000ff00#64, 0xffffffffffffffff#64]
