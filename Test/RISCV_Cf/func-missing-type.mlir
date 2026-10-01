// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f"}> ({}) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: missing 'function_type' property
