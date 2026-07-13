// RUN: veir-interpret %s | filecheck %s

// Executing `llvm.unreachable` is immediate undefined behaviour.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
