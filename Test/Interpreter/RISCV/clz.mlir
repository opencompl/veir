// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !riscv.reg
    %d = "riscv.clz"(%a) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.clz"(%b) : (!riscv.reg) -> !riscv.reg
    %f = "riscv.clz"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%d, %e, %f) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000003e#64, 0x0000000000000000#64, 0x000000000000001f#64]
