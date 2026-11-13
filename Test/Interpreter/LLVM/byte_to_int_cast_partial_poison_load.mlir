// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// NO_CROSS_CHECK: a cast of the `llvm.byte` type, which is not LLVM.

// Storing the `i8`s 0x34 and 0x12 into bytes 3 and 4, the center of an 8-byte
// `alloca`, leaves the three bytes below and the three bytes above them
// uninitialized, and so poison. A `!llvm.byte<64>` load yields a byte value
// that has a mix of poisonous and non-poison bits. The poison bits are
// non-deterministically chosen by a ctree effect and are set to zero by
// the default effect handler.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %low = "llvm.mlir.constant"() <{value = 0x34 : i8}> : () -> i8
    %high = "llvm.mlir.constant"() <{value = 0x12 : i8}> : () -> i8
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %p3 = "llvm.getelementptr"(%p, %three) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %p4 = "llvm.getelementptr"(%p, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%low, %p3) : (i8, !llvm.ptr) -> ()
    "llvm.store"(%high, %p4) : (i8, !llvm.ptr) -> ()
    %b = "llvm.load"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %i = "builtin.unrealized_conversion_cast"(%b) : (!llvm.byte<64>) -> i64
    "llvm.return"(%i) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000001234000000#64]
