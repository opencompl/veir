// RUN: veir-interpret %s | filecheck %s

// A `g_store` with a `size` smaller than its value only writes the low `size`
// bits.
// This test confirms this behavior: We store 8 bits of an `i64` over 0x11223344
// and ensure that only the lowest byte changes.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %c = "llvm.mlir.constant"() <{value = 0x11223344 : i32}> : () -> i32
    "gmir.g_store"(%c, %p) <{alignment = 4 : i64, size = 32 : i64}> : (i32, !llvm.ptr) -> ()
    %v = "llvm.mlir.constant"() <{value = 0x7766 : i64}> : () -> i64
    "gmir.g_store"(%v, %p) <{alignment = 1 : i64, size = 8 : i64}> : (i64, !llvm.ptr) -> ()
    %x = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x11223366#32]
