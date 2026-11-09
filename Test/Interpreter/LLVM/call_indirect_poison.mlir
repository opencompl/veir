// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: LLUBI

// Calling a poison pointer is undefined behavior.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    "llvm.call"(%p) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
