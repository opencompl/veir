// RUN: veir-interpret %s | filecheck %s

// An explicit `alignment = 1` permits an i32 access at offset 2.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %two) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %q) <{alignment = 1 : i64}> : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%q) <{alignment = 1 : i64}> : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000005#32]
