// RUN: veir-interpret %s | filecheck %s
// RUN: veir-interpret --ctree %s | filecheck %s

// A `g_load` with a `size` smaller than its result reads `size` bits and
// leaves the high bits unspecified, as `g_anyext` does.
// This test confirms this behavior: We load 8 bits of 0x11223344 into an `i64`
// and ensure that the result is 0x44, since both interpreters set the high bits
// to 0 by default.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %c = "llvm.mlir.constant"() <{value = 0x11223344 : i32}> : () -> i32
    "gmir.g_store"(%c, %p) <{alignment = 4 : i64, size = 32 : i64}> : (i32, !llvm.ptr) -> ()
    %x = "gmir.g_load"(%p) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%x) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000044#64]
