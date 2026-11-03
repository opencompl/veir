// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  %f = "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({}) : () -> !riscv.reg
}) : () -> ()

// CHECK: riscv_cf.func: Expected 0 results
