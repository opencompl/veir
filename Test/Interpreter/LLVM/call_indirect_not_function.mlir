// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: LLUBI

// Calling a pointer to an object that is not a function is undefined behavior.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "llvm.call"(%p) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
