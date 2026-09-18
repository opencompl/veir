// RUN: veir-interpret %s | filecheck %s

// A load from an address that no allocation covers is UB; memory does not
// grow under machine-code accesses.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !riscv.reg}> ({
    %a = "riscv.li"() <{ "value" = 4096 : i64 }> : () -> !riscv.reg
    %y = "riscv.ld"(%a) <{ "value" = 0 : i64 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
