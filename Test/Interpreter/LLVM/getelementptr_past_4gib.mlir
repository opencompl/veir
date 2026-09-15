// RUN: veir-interpret %s | filecheck %s

// Pointer offsets are 64 bits wide. Stepping 4 GiB past an 8-byte object
// leaves it, so the load is UB rather than wrapping back to the start.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %seven = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %far = "llvm.mlir.constant"() <{value = 4294967296 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%seven, %p) : (i64, !llvm.ptr) -> ()
    %q = "llvm.getelementptr"(%p, %far) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
