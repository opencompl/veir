// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %e = "riscv.li"() <{ value = -3 : i64 }> : () -> !riscv.reg
    %f = "riscv.mul"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.mul"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %h = "riscv.mul"(%d, %e) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%f, %g, %h) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000000a#64, 0xfffffffffffffff6#64, 0xfffffffcfffffffa#64]
