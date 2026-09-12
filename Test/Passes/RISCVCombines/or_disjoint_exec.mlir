// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv-combine > %t
// RUN: veir-interpret %t | filecheck %s

// Block arguments prevent constant folding from bypassing the OR rewrites.
// Removing an AND can make previously disjoint OR operands overlap.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    "cf.br"(%one, %zero, %one) [^test] : (i8, i8, i8) -> ()
  ^test(%x: i8, %y: i8, %z: i8):
    %ones = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %ny = "llvm.xor"(%y, %ones) : (i8, i8) -> i8
    %xy = "llvm.and"(%x, %y) : (i8, i8) -> i8
    // (1 & 0) | ~0 = 255, but 1 and ~0 overlap after removing the AND.
    %r1 = "llvm.or"(%xy, %ny) <{isDisjoint}> : (i8, i8) -> i8
    %nz = "llvm.xor"(%z, %ones) : (i8, i8) -> i8
    %xnz = "llvm.and"(%x, %nz) : (i8, i8) -> i8
    // (1 & ~1) | 1 = 1, but 1 and 1 overlap after removing the AND.
    %r2 = "llvm.or"(%xnz, %z) <{isDisjoint}> : (i8, i8) -> i8
    "func.return"(%r1, %r2) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, 0x01#8]
