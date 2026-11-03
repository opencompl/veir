// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i64) -> ()}> ({
  ^bb0(%x : i64):
    %a = "riscv.li"() <{ "value" = 1 : i64 }> : () -> !riscv.reg
    %b = "riscv.add"(%x, %a) : (i64, !riscv.reg) -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Error verifying input program: riscv.add: Expected operand 0 to have !riscv.reg type
