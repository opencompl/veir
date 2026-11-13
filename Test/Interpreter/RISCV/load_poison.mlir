// RUN: veir-interpret %s | filecheck %s
// RUN: veir-interpret --ctree %s | filecheck %s

// Registers cannot carry poison, so a load chooses the bits of the loaded bytes
// that are poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %a = "riscv_stack.alloca"() <{ "size" = 2 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 255 : i64 }> : () -> !riscv.reg
    "riscv.sb"(%x, %a) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    %h = "riscv.lh"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    %b = "riscv.lbu"(%a) <{ "value" = 1 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%h, %b) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000ff#64, 0x0000000000000000#64]
