// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = (!riscv.reg<x10>) -> ()}> ({
  ^entry(%a: !riscv.reg<x11>):
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: Entry block argument 0 type does not match function signature
