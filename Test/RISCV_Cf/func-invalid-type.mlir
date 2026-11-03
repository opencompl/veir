// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.func"() <{sym_name = "f", function_type = !llvm.func<void ()>}> ({}) : () -> ()
}) : () -> ()

// CHECK: riscv_cf.func: expected 'function_type' to be a builtin function type
