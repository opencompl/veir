// RUN: veir-interpret %s | filecheck %s
// RUN: ALIVE_EXEC

// LLUBI: cannot cross-check this test: it returns a pointer, which the
// comparison does not know how to read.


// A ptr value loaded from a stack-allocated pointer that was never written to
// is poison.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.ptr ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %p = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
