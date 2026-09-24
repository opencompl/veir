// RUN: veir-interpret %s | filecheck %s

// Executing `riscv_cf.unreachable` is immediate undefined behaviour.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "riscv_cf.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
