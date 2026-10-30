// RUN: not veir-opt %s -p=register-allocation-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "g", function_type = (!riscv.reg) -> ()}> ({
  ^entry(%a : !riscv.reg):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation does not support block arguments
