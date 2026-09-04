// RUN: veir-interpret %s | filecheck %s

// Send `abcd` to our own address, clear the buffer, receive it back, and
// return the bytes sent, the bytes received, the buffer contents, and the
// sender. The interpreter assigns itself address 0.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i32, !io.address)}> ({
    %self = "io.self"() : () -> !io.address
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %abcd = "llvm.mlir.constant"() <{value = 1684234849 : i32}> : () -> i32
    "llvm.store"(%abcd, %buf) : (i32, !llvm.ptr) -> ()
    %sent = "io.send"(%self, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.store"(%zero, %buf) : (i32, !llvm.ptr) -> ()
    %received, %from = "io.recv"(%buf, %len) : (!llvm.ptr, i64) -> (i64, !io.address)
    %back = "llvm.load"(%buf) : (!llvm.ptr) -> i32
    "func.return"(%sent, %received, %back, %from) : (i64, i64, i32, !io.address) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000004#64, 0x0000000000000004#64, 0x64636261#32, ioAddr(0)]
