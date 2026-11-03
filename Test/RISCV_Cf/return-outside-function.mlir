// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "riscv_cf.return"() : () -> ()
}) : () -> ()

// CHECK: Expected riscv_cf.return to be enclosed by a function-like operation
