// RUN: veir-interpret %s | filecheck %s

// `memcpy` requires its two ranges to be equal or disjoint. Copying 16 bytes
// from offset 8 of a 24-byte object to its start overlaps, so it is UB.
// `memmove` is the operation that allows this.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %sixteen = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %p = "llvm.alloca"(%three) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %eight) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%p, %q, %sixteen) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %v = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
