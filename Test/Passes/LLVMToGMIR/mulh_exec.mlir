// RUN: veir-interpret %s | filecheck %s
// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir > %t
// RUN: filecheck %s --input-file=%t --check-prefix=GMIR
// RUN: veir-interpret %t | filecheck %s
// RUN: veir-interpret --ctree %t | filecheck %s

// `llvm.intr.smulh` and `llvm.intr.umulh` become the generic opcodes, and the
// program computes the same values before and after. The second column tells
// the two apart: the bits of -100 are 156 read unsigned.

// GMIR:     "gmir.g_smulh"(%{{.*}}, %{{.*}}) : (i8, i8) -> i8
// GMIR:     "gmir.g_umulh"(%{{.*}}, %{{.*}}) : (i8, i8) -> i8
// GMIR-NOT: llvm.intr.smulh
// GMIR-NOT: llvm.intr.umulh

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8)}> ({
    %c100 = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %c50 = "llvm.mlir.constant"() <{ "value" = 50 : i8 }> : () -> i8
    %cn100 = "llvm.mlir.constant"() <{ "value" = -100 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    %s1 = "llvm.intr.smulh"(%c100, %c50) : (i8, i8) -> i8
    %s2 = "llvm.intr.smulh"(%cn100, %c50) : (i8, i8) -> i8
    %u1 = "llvm.intr.umulh"(%c100, %c50) : (i8, i8) -> i8
    %u2 = "llvm.intr.umulh"(%cn100, %c50) : (i8, i8) -> i8
    %p = "llvm.intr.smulh"(%c100, %poison) : (i8, i8) -> i8
    "func.return"(%s1, %s2, %u1, %u2, %p) : (i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x13#8, 0xec#8, 0x13#8, 0x1e#8, poison]
