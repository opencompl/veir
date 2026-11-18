// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE

// `g_ptr_add` adds a byte offset to a pointer.
// We store 0x0100 as an `i64` and load the byte at offset 1, which is 1.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %c = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    "gmir.g_store"(%c, %p) <{alignment = 8 : i64, size = 64 : i64}> : (i64, !llvm.ptr) -> ()
    %q = "gmir.g_ptr_add"(%p, %one) : (!llvm.ptr, i64) -> !llvm.ptr
    %x = "gmir.g_load"(%q) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i8
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x01#8]
