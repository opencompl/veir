// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %base = "riscv_stack.alloca"() <{ "size" = 16 : i64, "alignment" = 8 : i64 }> : () -> !riscv.reg
    %x = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !riscv.reg
    // store to effective address base + 8 (positive immediate offset)
    "riscv.sd"(%x, %base) <{ "value" = 8 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    // load from base + 16 with offset -8, reaching the same effective address base + 8
    %hi = "riscv.addi"(%base) <{ value = 16 : i64 }> : (!riscv.reg) -> !riscv.reg
    %y = "riscv.ld"(%hi) <{ "value" = -8 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000122#64]
