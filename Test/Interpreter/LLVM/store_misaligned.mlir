// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// An `llvm.store` without an `alignment` attribute requires the ABI alignment
// of its value: an i32 stored at offset 2 of an i64 slot is in bounds but not
// 4-byte aligned, so it is undefined behaviour.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p2 = "llvm.getelementptr"(%p, %two) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %p2) : (i32, !llvm.ptr) -> ()
    "func.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
