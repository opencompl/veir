// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir
// RUN: filecheck %s --check-prefix=LEGAL < %t.gmir
// RUN: veir-interpret %t.gmir | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t | filecheck %s

// Narrow block arguments are widened to i64: the loop-carried i32 values and the i32 exit value.
// The entry block's argument-free signature is untouched.

// LEGAL: ^{{.*}}(%{{.*}} : i64, %{{.*}} : i64):
// LEGAL: ^{{.*}}(%{{.*}} : i64):

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
  ^bb0:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %n = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    "llvm.br"(%zero, %zero) [^loop] : (i32, i32) -> ()
  ^loop(%i : i32, %s : i32):
    %s1 = "llvm.add"(%s, %i) : (i32, i32) -> i32
    %i1 = "llvm.add"(%i, %one) : (i32, i32) -> i32
    %c = "llvm.icmp"(%i1, %n) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%c, %i1, %s1, %s1) [^loop, ^exit] <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (i1, i32, i32, i32) -> ()
  ^exit(%r : i32):
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000a#32]
