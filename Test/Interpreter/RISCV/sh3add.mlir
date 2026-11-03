// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %f = "riscv.sh3add"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.sh3add"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %h = "riscv.sh3add"(%d, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%f, %g, %h) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000015#64, 0x000000000000000b#64, 0x0000000800000012#64]
