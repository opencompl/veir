// RUN: veir-interpret %s | filecheck %s

// `memmove` may overlap. Copying the second half of the object over the
// first moves the value stored at offset 8 to offset 0.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %sixteen = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %val = "llvm.mlir.constant"() <{value = 77 : i64}> : () -> i64
    %p = "llvm.alloca"(%three) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %eight) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%val, %q) : (i64, !llvm.ptr) -> ()
    "llvm.intr.memmove"(%p, %q, %sixteen) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %v = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000004d#64]
