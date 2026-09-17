// RUN: veir-interpret %s | filecheck %s

// The operation `llvm.mlir.zero` yields the zero address (null-pointer). Bitcasting it gives that address
// with no poison bits, both as an `llvm.byte` and as an integer.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.ptr, !llvm.byte<64>, i64)}> ({
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %byte = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %int = "llvm.bitcast"(%p) : (!llvm.ptr) -> i64
    "func.return"(%p, %byte, %int) : (!llvm.ptr, !llvm.byte<64>, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[ptr(0x0000000000000000), 0b0000000000000000000000000000000000000000000000000000000000000000#64, 0x0000000000000000#64]
