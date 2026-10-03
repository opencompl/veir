// RUN: veir-interpret %s | filecheck %s

// `llvm.bitcast` reinterprets an integer as an `llvm.byte` of the same width:
// the bits are the integer's, and none of them is poison.
//
// The cross-checks cannot read this test. LLVM 23 has the byte type, `bN`,
// but alive-exec rejects it, and llubi reads one back as zero, so neither can
// say what this test asserts. The translator leaves the type alone until they
// can.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.byte<64> ()>}> ({
    %c = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %b = "llvm.bitcast"(%c) : (i64) -> !llvm.byte<64>
    "llvm.return"(%b) : (!llvm.byte<64>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b0000000000000000000000000000000000000000000000000000000000010001#64]
