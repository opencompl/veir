// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !riscv.reg
    %e = "riscv.packh"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %f = "riscv.packh"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.packh"(%a, %d) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%e, %f, %g) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000502#64, 0x000000000000fb02#64, 0x0000000000000102#64]
