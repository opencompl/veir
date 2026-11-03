// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI_CHECK
// RUN: ALIVE_EXEC_CHECK

// Freezing a poison pointer yields some pointer; the interpreter picks null.
// llubi and alive-exec pick some pointer as well; which one is theirs to choose.
// In the future, we would like to use ctrees to enable a non-determistic choice,
// at least in our model.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.ptr ()>}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %f = "llvm.freeze"(%p) : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%f) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[ptr(0, 0)]
// ALIVE_EXEC: Program output: #[ptr]
// LLUBI: Program output: #[ptr]
