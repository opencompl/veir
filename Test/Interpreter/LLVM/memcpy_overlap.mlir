// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// `llvm.intr.memcpy` with partially overlapping ranges is UB.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %buf = "llvm.alloca"(%two) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%one, %buf) : (i64, !llvm.ptr) -> ()
    %buf1 = "llvm.getelementptr"(%buf, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%buf1, %buf, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
