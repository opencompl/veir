// RUN: veir-interpret %s | filecheck %s

// A 4-byte message received into a 2-byte window reports
// `Io.Error.messageTooLong` (-3), leaves the buffer untouched, and stays in
// flight, so a retry with the full length succeeds with 4 bytes.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i32, i64, i32)}> ({
    %self = "io.self"() : () -> !io.address
    %len = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %short = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %buf = "llvm.alloca"(%len) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %abcd = "llvm.mlir.constant"() <{value = 1684234849 : i32}> : () -> i32
    "llvm.store"(%abcd, %buf) : (i32, !llvm.ptr) -> ()
    %sent = "io.send"(%self, %buf, %len) : (!io.address, !llvm.ptr, i64) -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    "llvm.store"(%zero, %buf) : (i32, !llvm.ptr) -> ()
    %n1, %from1 = "io.recv"(%buf, %short) : (!llvm.ptr, i64) -> (i64, !io.address)
    %w1 = "llvm.load"(%buf) : (!llvm.ptr) -> i32
    %n2, %from2 = "io.recv"(%buf, %len) : (!llvm.ptr, i64) -> (i64, !io.address)
    %w2 = "llvm.load"(%buf) : (!llvm.ptr) -> i32
    "func.return"(%n1, %w1, %n2, %w2) : (i64, i32, i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffd#64, 0x00000000#32, 0x0000000000000004#64, 0x64636261#32]
