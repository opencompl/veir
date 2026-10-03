// RUN: veir-interpret %s | filecheck %s

// The operation `llvm.mlir.zero` yields the zero address (null-pointer). `llvm.ptrtoint`
// gives that address with no poison bits, and bitcasting it gives the same as an `llvm.byte`.
// Alive2 agrees (alive-exec): `ptrtoint` of null returns 0, non-poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.ptr, !llvm.byte<64>, i64)}> ({
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %int = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %byte = "llvm.bitcast"(%int) : (i64) -> !llvm.byte<64>
    "func.return"(%p, %byte, %int) : (!llvm.ptr, !llvm.byte<64>, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[ptr(0, 0), 0b0000000000000000000000000000000000000000000000000000000000000000#64, 0x0000000000000000#64]
