// RUN: veir-interpret %s | filecheck %s
// NO_CROSS_CHECK: the `llvm.byte` type: alive-exec rejects it and llubi crashes on it.

// A `trunc` of a byte with `nsw` or `nuw` is poison if the dropped bits are not a sign or zero
// extension of the result, as for integers.
// This test confirms this behavior: We truncate 0x0080 and 0xff80 to 8 bits and ensure that `nsw`
// only rejects the first, and `nuw` only the second.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>)}> ({
    %x_i16 = "llvm.mlir.constant"() <{ "value" = 128 : i16 }> : () -> i16
    %y_i16 = "llvm.mlir.constant"() <{ "value" = -128 : i16 }> : () -> i16
    %x = "llvm.bitcast"(%x_i16) : (i16) -> !llvm.byte<16>
    %y = "llvm.bitcast"(%y_i16) : (i16) -> !llvm.byte<16>
    %x_nsw = "llvm.trunc"(%x) <{"overflowFlags" = 1 : i32}> : (!llvm.byte<16>) -> !llvm.byte<8>
    %x_nuw = "llvm.trunc"(%x) <{"overflowFlags" = 2 : i32}> : (!llvm.byte<16>) -> !llvm.byte<8>
    %y_nsw = "llvm.trunc"(%y) <{"overflowFlags" = 1 : i32}> : (!llvm.byte<16>) -> !llvm.byte<8>
    %y_nuw = "llvm.trunc"(%y) <{"overflowFlags" = 2 : i32}> : (!llvm.byte<16>) -> !llvm.byte<8>
    "func.return"(%x_nsw, %x_nuw, %y_nsw, %y_nuw) : (!llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>, !llvm.byte<8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b????????#8, 0b10000000#8, 0b10000000#8, 0b????????#8]
