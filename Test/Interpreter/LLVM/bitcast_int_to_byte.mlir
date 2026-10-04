// RUN: veir-interpret %s | filecheck %s

// `llvm.bitcast` reinterprets an integer as an `llvm.byte` of the same width:
// the bits are the integer's, and none of them is poison.
//
// The cross-checks cannot read this test: alive-exec rejects the byte type,
// and llubi gives a byte-typed result no value.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.byte<64> ()>}> ({
    %c = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %b = "llvm.bitcast"(%c) : (i64) -> !llvm.byte<64>
    "llvm.return"(%b) : (!llvm.byte<64>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b0000000000000000000000000000000000000000000000000000000000010001#64]
