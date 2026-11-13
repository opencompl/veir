// RUN: veir-interpret %s | filecheck %s
// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir > %t
// RUN: filecheck %s --input-file=%t --check-prefix=GMIR
// RUN: veir-interpret %t | filecheck %s
// RUN: veir-interpret --ctree %t | filecheck %s

// A byte `llvm.mlir.poison` is wholly poison. It becomes `g_poison` on the integer of the same
// width, which casts to the same wholly poison byte.

// GMIR:     "gmir.g_poison"() : () -> i64
// GMIR-NOT: llvm.mlir.poison

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %b = "llvm.mlir.poison"() : () -> !llvm.byte<64>
    %t8 = "llvm.trunc"(%b) : (!llvm.byte<64>) -> !llvm.byte<8>
    %r = "llvm.bitcast"(%t8) : (!llvm.byte<8>) -> i8
    %z = "llvm.zext"(%r) : (i8) -> i64
    "llvm.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
