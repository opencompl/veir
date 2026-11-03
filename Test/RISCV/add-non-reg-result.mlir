// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %b = "riscv.add"(%a, %a) : (!riscv.reg, !riscv.reg) -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error verifying input program: riscv.add: Expected result 0 to have !riscv.reg type
