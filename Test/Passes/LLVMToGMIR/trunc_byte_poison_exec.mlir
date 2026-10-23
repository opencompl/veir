// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir > %t && veir-interpret %t | filecheck %s --check-prefix=GMIR

// A wholly poison byte stays poison in gMIR. It is loaded from memory, as casting a poison integer
// to a byte and back folds away.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %poison = "llvm.mlir.poison"() : () -> i64
    "llvm.store"(%poison, %p) : (i64, !llvm.ptr) -> ()
    %b = "llvm.load"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %t8 = "llvm.trunc"(%b) : (!llvm.byte<64>) -> !llvm.byte<8>
    %r = "llvm.bitcast"(%t8) : (!llvm.byte<8>) -> i8
    %z = "llvm.zext"(%r) : (i8) -> i64
    "llvm.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[poison]
// GMIR:  Program output: #[poison]
