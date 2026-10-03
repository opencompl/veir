// RUN: veir-interpret %s | filecheck %s

// `llvm.ptrtoint` of a poison pointer gives a poison integer, and bitcasting that gives an
// `llvm.byte` whose every bit is poison.
// Alive2 agrees (alive-exec): `ptrtoint` of poison returns poison.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<64>, i64)}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %int = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %byte = "llvm.bitcast"(%int) : (i64) -> !llvm.byte<64>
    "func.return"(%byte, %int) : (!llvm.byte<64>, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b????????????????????????????????????????????????????????????????#64, poison]
