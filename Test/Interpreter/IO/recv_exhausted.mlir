// RUN: veir-interpret %s | filecheck %s

// Receiving with nothing in flight reports `Io.Error.exhausted` (-2); the
// sender result is unspecified and the interpreter returns address 0.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, !io.address)}> ({
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %n, %from = "io.recv"(%buf, %len) : (!llvm.ptr, i64) -> (i64, !io.address)
    "func.return"(%n, %from) : (i64, !io.address) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffe#64, ioAddr(0)]
