// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: LLUBI

// Calling a pointer past the start of a function is undefined behavior.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<void ()>}> ({
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @f}> : () -> !llvm.ptr
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.getelementptr"(%f, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.call"(%p) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
