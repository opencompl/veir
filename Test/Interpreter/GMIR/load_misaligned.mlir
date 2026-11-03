// RUN: veir-interpret %s | filecheck %s

// A `g_load` from an address that is not a multiple of its `alignment` is
// undefined behavior.
// This test confirms this behavior: We load an `i32` with `alignment = 4` from
// an address that is only 2-byte aligned and ensure that the interpreter
// reports undefined behavior.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p2 = "llvm.getelementptr"(%p, %two) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %x = "gmir.g_load"(%p2) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
