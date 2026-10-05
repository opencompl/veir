// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: Expected 1 region
