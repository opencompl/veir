// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// `llvm.ptrtoint` of a poison pointer gives a poison integer.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %int = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%int) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
