// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// Byte truncations go through gMIR as integer truncations, and the casts between them fold away.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %c = "llvm.mlir.constant"() <{value = 0x11223344AABBCCDD : i64}> : () -> i64
    %b = "llvm.bitcast"(%c) : (i64) -> !llvm.byte<64>
    %t32 = "llvm.trunc"(%b) : (!llvm.byte<64>) -> !llvm.byte<32>
    %t8 = "llvm.trunc"(%t32) : (!llvm.byte<32>) -> !llvm.byte<8>
    %r = "llvm.bitcast"(%t8) : (!llvm.byte<8>) -> i8
    %z = "llvm.zext"(%r) : (i8) -> i64
    "llvm.return"(%z) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000000000000dd#64]
// CHECK: Program output: #[0x00000000000000dd#64]
