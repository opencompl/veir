// RUN: veir-interpret %s | filecheck %s

// A `g_load` of a pointer returns the pointer that a `g_store` wrote.
// This test confirms this behavior: We store a pointer to an `i32`, load it
// back and ensure that reading through it gives the `i32`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %c = "llvm.mlir.constant"() <{value = 42 : i32}> : () -> i32
    "gmir.g_store"(%c, %p) <{alignment = 4 : i64, size = 32 : i64}> : (i32, !llvm.ptr) -> ()
    "gmir.g_store"(%p, %q) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    %r = "gmir.g_load"(%q) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %x = "llvm.load"(%r) : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
