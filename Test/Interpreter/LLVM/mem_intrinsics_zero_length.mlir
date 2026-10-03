// RUN: veir-interpret %s | filecheck %s

// A memory intrinsic of length zero touches no memory, so its pointers may be
// null or poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %len = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %byte = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %null = "llvm.mlir.zero"() : () -> !llvm.ptr
    %poison = "llvm.mlir.poison"() : () -> !llvm.ptr
    "llvm.intr.memset"(%poison, %byte, %len) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%null, %poison, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memmove"(%poison, %null, %len) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "func.return"(%len) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
