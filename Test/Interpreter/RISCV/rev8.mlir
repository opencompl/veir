// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 1 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 255 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 72623859790382856 : i64 }> : () -> !riscv.reg
    %d = "riscv.rev8"(%a) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.rev8"(%b) : (!riscv.reg) -> !riscv.reg
    %f = "riscv.rev8"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%d, %e, %f) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0100000000000000#64, 0xff00000000000000#64, 0x0807060504030201#64]
