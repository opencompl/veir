// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir && veir-interpret %t.gmir | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: filecheck %s --check-prefix=ASM < %t
// RUN: veir-interpret %t | filecheck %s

// The loop-carried i32 and i8 values and the i8 exit value are widened to i64, so they need no
// extension at the branches.

// ASM-NOT: "riscv.zext

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
  ^bb0:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %two = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %zero8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %one8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    "llvm.br"(%zero, %zero8) [^loop] : (i32, i8) -> ()
  ^loop(%i : i32, %s : i8):
    %s1 = "llvm.add"(%s, %one8) : (i8, i8) -> i8
    %i1 = "llvm.add"(%i, %one) : (i32, i32) -> i32
    %c = "llvm.icmp"(%i1, %two) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%c, %i1, %s1, %s1) [^loop, ^exit] <{operandSegmentSizes = array<i32: 1, 2, 1>}> : (i1, i32, i8, i8) -> ()
  ^exit(%r : i8):
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x02#8]
