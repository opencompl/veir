// RUN: veir-interpret %s | filecheck %s

// Executing `llvm.unreachable` is immediate undefined behaviour.
"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
