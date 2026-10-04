// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// Executing `llvm.unreachable` is immediate undefined behaviour.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
