// RUN: veir-interpret %s | filecheck %s
// RUN: ALIVE_EXEC

// LLUBI: cannot cross-check this test: it returns a pointer, which the
// comparison does not know how to read.


// Offsetting a poison pointer gives a poison pointer.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.ptr ()>}> ({
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %q = "llvm.getelementptr"(%p, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%q) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
