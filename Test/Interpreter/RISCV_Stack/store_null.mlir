// RUN: veir-interpret %s | filecheck %s

// A store to address 0 is UB.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    %v = "riscv.li"() <{ "value" = 42 : i64 }> : () -> !riscv.reg
    %p = "riscv.li"() <{ "value" = 0 : i64 }> : () -> !riscv.reg
    "riscv.sd"(%v, %p) <{ "value" = 0 : i64 }> : (!riscv.reg, !riscv.reg) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
