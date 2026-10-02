// RUN: veir-interpret %s | filecheck %s

// A byte can be partly poison. A `b8` load keeps its poison bits, and so does
// `llvm.intr.memcpy`, which copies one `b8` at a time.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<8>, !llvm.byte<64>)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %val = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %poison = "llvm.mlir.poison"() : () -> i8
    %src = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %src4 = "llvm.getelementptr"(%src, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%val, %src) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%poison, %src4) : (i8, !llvm.ptr) -> ()
    %b = "llvm.load"(%src) : (!llvm.ptr) -> !llvm.byte<64>
    %shifted = "llvm.shl"(%b, %four) : (!llvm.byte<64>, i64) -> !llvm.byte<64>
    "llvm.store"(%shifted, %src) : (!llvm.byte<64>, !llvm.ptr) -> ()
    %dst = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%dst, %src, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %dst4 = "llvm.getelementptr"(%dst, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %part = "llvm.load"(%dst4) : (!llvm.ptr) -> !llvm.byte<8>
    %copy = "llvm.load"(%dst) : (!llvm.ptr) -> !llvm.byte<64>
    "func.return"(%part, %copy) : (!llvm.byte<8>, !llvm.byte<64>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b????0000#8, 0b00000000000000000000????????000000000000000000000000000100010000#64]
