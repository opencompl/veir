// RUN: veir-interpret %s | filecheck %s
// NO_CROSS_CHECK: the `llvm.byte` type: alive-exec rejects it and llubi crashes on it.

// The operation `llvm.mlir.zero` yields the zero address (null-pointer).
// Bitcasting it to an `llvm.byte` gives that address with no poison bits.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.ptr, !llvm.byte<64>)}> ({
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %byte = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    "func.return"(%p, %byte) : (!llvm.ptr, !llvm.byte<64>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[ptr(0, 0), 0b0000000000000000000000000000000000000000000000000000000000000000#64]
