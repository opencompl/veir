// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{function_type = () -> ()}> ({}) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: missing 'sym_name' property
