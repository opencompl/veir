// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg<x10>) -> ()}> ({
  ^entry(%a: !riscv.reg<x11>):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: type of entry block argument #0(!riscv.reg<x11>) must match the type of the corresponding argument in function signature(!riscv.reg<x10>)
