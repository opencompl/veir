// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// Storing past the end of an `alloca` is UB.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p1 = "llvm.getelementptr"(%p, %eight) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%eight, %p1) : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
