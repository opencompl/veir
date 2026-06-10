// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 0 : i64 }> : () -> !riscv.reg
    %y = "riscv.ld"(%a) <{ "value" = -2049 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error verifying input program: riscv.ld immediate out of bounds: must fit in a signed 12-bit field [-2048, 2047]
