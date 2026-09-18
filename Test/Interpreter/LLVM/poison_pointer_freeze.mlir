// RUN: veir-interpret %s | filecheck %s

// Freezing a poison pointer yields some pointer; the interpreter picks null.
// In the future, we would like to use ctrees to enable a non-determistic choice,
// at least in our model.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !llvm.ptr}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %f = "llvm.freeze"(%p) : (!llvm.ptr) -> !llvm.ptr
    "func.return"(%f) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[ptr(0, 0)]
