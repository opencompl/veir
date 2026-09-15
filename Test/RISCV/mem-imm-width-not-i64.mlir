// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 0 : i64 }> : () -> !riscv.reg
    %y = "riscv.ld"(%a) <{ "value" = 8 : i12 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: RISC-V memory operation: expected 'value' to be a 64-bit integer attribute, but got i12
