// RUN: veir-interpret %s | filecheck %s

// A `g_load` is poison if every bit it loads is poison, as in fresh memory.
// This test confirms this behavior: We load an `i32` from a new allocation and
// ensure that the result is poison.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %x = "gmir.g_load"(%p) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
