// RUN: not veir-opt %s -p=register-allocation-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg) -> ()}> ({
  ^entry(%a : !riscv.reg):
    %sum = "riscv.add"(%a, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation does not support block arguments
