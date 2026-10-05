// RUN: veir-interpret %s | filecheck %s

// Bitcasting a poison pointer gives a value whose bits are all poison: every
// bit of an `llvm.byte` is poison, and an integer is poison as a whole.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<64>, i64)}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %byte = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %int = "llvm.bitcast"(%p) : (!llvm.ptr) -> i64
    "func.return"(%byte, %int) : (!llvm.byte<64>, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b????????????????????????????????????????????????????????????????#64, poison]
