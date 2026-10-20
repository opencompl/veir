// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir > %t && veir-interpret %t | filecheck %s --check-prefix=GMIR

// A wholly poison byte stays poison in gMIR.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %poison = "llvm.mlir.poison"() : () -> i16
    %b = "llvm.bitcast"(%poison) : (i16) -> !llvm.byte<16>
    %t8 = "llvm.trunc"(%b) : (!llvm.byte<16>) -> !llvm.byte<8>
    %r = "llvm.bitcast"(%t8) : (!llvm.byte<8>) -> i8
    %z = "llvm.zext"(%r) : (i8) -> i64
    "llvm.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[poison]
// GMIR:  Program output: #[poison]
