// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI
// RUN: ALIVE_EXEC

// A poison `i12` is stored in two poison bytes, and loading it back gives poison.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i12 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i16}> : () -> i16
    %v = "llvm.mlir.poison"() : () -> i12
    %p = "llvm.alloca"(%one) <{elem_type = i16}> : (i64) -> !llvm.ptr
    "llvm.store"(%zero, %p) : (i16, !llvm.ptr) -> ()
    "llvm.store"(%v, %p) : (i12, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i12
    "llvm.return"(%r) : (i12) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
