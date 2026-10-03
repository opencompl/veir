// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// The operation `llvm.mlir.zero` yields the null pointer, and `llvm.ptrtoint`
// gives its address, which is zero and carries no poison. Reinterpreting an
// address as an `llvm.byte` is `bitcast`'s own test.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %int = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%int) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
