// RUN: veir-interpret %s | filecheck %s

// A poison integer reinterpreted as an `llvm.byte` has every bit poison,
// where the integer was poison as a whole.
//
// The cross-checks cannot read this test. LLVM 23 has the byte type, `bN`,
// but alive-exec rejects it, and llubi reads one back as zero, so neither can
// say what this test asserts. The translator leaves the type alone until they
// can.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.byte<64> ()>}> ({
    %p = "llvm.mlir.poison"() : () -> i64
    %b = "llvm.bitcast"(%p) : (i64) -> !llvm.byte<64>
    "llvm.return"(%b) : (!llvm.byte<64>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0b????????????????????????????????????????????????????????????????#64]
