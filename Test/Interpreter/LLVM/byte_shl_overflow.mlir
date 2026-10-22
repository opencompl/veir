// RUN: veir-interpret %s | filecheck %s
// NO_CROSS_CHECK: the `llvm.byte` type: alive-exec rejects it and llubi crashes on it.

// A `shl` of a byte with `nsw` or `nuw` is poison if the shifted out bits are not zero or do not
// agree with the sign bit of the result, as for integers.
// This test confirms this behavior: We shift 0x40 and 0xc0 left by one and ensure that `nsw` only
// rejects the first, and `nuw` only the second.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>)}> ({
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %x_i8 = "llvm.mlir.constant"() <{ "value" = 64 : i8 }> : () -> i8
    %y_i8 = "llvm.mlir.constant"() <{ "value" = -64 : i8 }> : () -> i8
    %x = "llvm.bitcast"(%x_i8) : (i8) -> !llvm.byte<8>
    %y = "llvm.bitcast"(%y_i8) : (i8) -> !llvm.byte<8>
    %x_nsw = "llvm.shl"(%x, %one) <{"overflowFlags" = 1 : i32}> : (!llvm.byte<8>, i8) -> !llvm.byte<8>
    %x_nuw = "llvm.shl"(%x, %one) <{"overflowFlags" = 2 : i32}> : (!llvm.byte<8>, i8) -> !llvm.byte<8>
    %y_nsw = "llvm.shl"(%y, %one) <{"overflowFlags" = 1 : i32}> : (!llvm.byte<8>, i8) -> !llvm.byte<8>
    %y_nuw = "llvm.shl"(%y, %one) <{"overflowFlags" = 2 : i32}> : (!llvm.byte<8>, i8) -> !llvm.byte<8>
    "func.return"(%x_nsw, %x_nuw, %y_nsw, %y_nuw) : (!llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b????????#8, 0b10000000#8, 0b10000000#8, 0b????????#8]
