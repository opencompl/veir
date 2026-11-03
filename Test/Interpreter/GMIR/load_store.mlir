// RUN: veir-interpret %s | filecheck %s

// A `g_store` with a `size` of the width of its value writes the whole value.
// This test confirms this behavior: We store 42 as an `i32` and ensure that a
// `g_load` of the same `size` reads 42.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %c = "llvm.mlir.constant"() <{value = 42 : i32}> : () -> i32
    "gmir.g_store"(%c, %p) <{alignment = 4 : i64, size = 32 : i64}> : (i32, !llvm.ptr) -> ()
    %x = "gmir.g_load"(%p) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
