// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> i64}> ({}) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: Expected register types in function signature
