// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv | veir-interpret | filecheck %s --check-prefix=RISCV

// Functional check for the `tryFoldSelectOfConstants` combines: each form on a true and on a false
// condition, and the source and the lowering must agree.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32)}> ({
    %a = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %ctrue = "llvm.icmp"(%a, %b) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %cfalse = "llvm.icmp"(%b, %a) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %t0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %f0 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %r0t = "llvm.select"(%ctrue, %t0, %f0) : (i1, i32, i32) -> i32
    %r0f = "llvm.select"(%cfalse, %t0, %f0) : (i1, i32, i32) -> i32
    %t1 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %f1 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %r1t = "llvm.select"(%ctrue, %t1, %f1) : (i1, i32, i32) -> i32
    %r1f = "llvm.select"(%cfalse, %t1, %f1) : (i1, i32, i32) -> i32
    %t2 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %f2 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %r2t = "llvm.select"(%ctrue, %t2, %f2) : (i1, i32, i32) -> i32
    %r2f = "llvm.select"(%cfalse, %t2, %f2) : (i1, i32, i32) -> i32
    %t3 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %f3 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %r3t = "llvm.select"(%ctrue, %t3, %f3) : (i1, i32, i32) -> i32
    %r3f = "llvm.select"(%cfalse, %t3, %f3) : (i1, i32, i32) -> i32
    %t4 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %f4 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %r4t = "llvm.select"(%ctrue, %t4, %f4) : (i1, i32, i32) -> i32
    %r4f = "llvm.select"(%cfalse, %t4, %f4) : (i1, i32, i32) -> i32
    %t5 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %f5 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %r5t = "llvm.select"(%ctrue, %t5, %f5) : (i1, i32, i32) -> i32
    %r5f = "llvm.select"(%cfalse, %t5, %f5) : (i1, i32, i32) -> i32
    %t6 = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
    %f6 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %r6t = "llvm.select"(%ctrue, %t6, %f6) : (i1, i32, i32) -> i32
    %r6f = "llvm.select"(%cfalse, %t6, %f6) : (i1, i32, i32) -> i32
    %t7 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %f7 = "llvm.mlir.constant"() <{value = 16 : i32}> : () -> i32
    %r7t = "llvm.select"(%ctrue, %t7, %f7) : (i1, i32, i32) -> i32
    %r7f = "llvm.select"(%cfalse, %t7, %f7) : (i1, i32, i32) -> i32
    %t8 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %f8 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %r8t = "llvm.select"(%ctrue, %t8, %f8) : (i1, i32, i32) -> i32
    %r8f = "llvm.select"(%cfalse, %t8, %f8) : (i1, i32, i32) -> i32
    %t9 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %f9 = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %r9t = "llvm.select"(%ctrue, %t9, %f9) : (i1, i32, i32) -> i32
    %r9f = "llvm.select"(%cfalse, %t9, %f9) : (i1, i32, i32) -> i32
    "func.return"(%r0t, %r0f, %r1t, %r1f, %r2t, %r2f, %r3t, %r3f, %r4t, %r4f, %r5t, %r5f, %r6t, %r6f, %r7t, %r7f, %r8t, %r8f, %r9t, %r9f) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x00000001#32, 0x00000000#32, 0xffffffff#32, 0x00000000#32, 0x00000000#32, 0x00000001#32, 0x00000000#32, 0xffffffff#32, 0x00000007#32, 0x00000006#32, 0x00000006#32, 0x00000007#32, 0x00000010#32, 0x00000000#32, 0x00000000#32, 0x00000010#32, 0xffffffff#32, 0x00000006#32, 0x00000006#32, 0xffffffff#32]
// RISCV: Program output: #[0x00000001#32, 0x00000000#32, 0xffffffff#32, 0x00000000#32, 0x00000000#32, 0x00000001#32, 0x00000000#32, 0xffffffff#32, 0x00000007#32, 0x00000006#32, 0x00000006#32, 0x00000007#32, 0x00000010#32, 0x00000000#32, 0x00000000#32, 0x00000010#32, 0xffffffff#32, 0x00000006#32, 0x00000006#32, 0xffffffff#32]
