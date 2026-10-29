// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64,isel-br-riscv64,isel-riscv64,isel-abi-riscv64,reconcile-cast,riscv-combine,dce > %t
// RUN: veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=SEL < %t

// Comparisons of i32, i8 and i16 values against constants select `slti`/`sltiu`: legalization
// sign-extends both operands, and the extension of the constant folds to an i64 constant. The
// `sle`/`ule` immediates are `C + 1`, and `sge`/`uge` invert the result with `xori`.

// SEL-COUNT-11: "riscv.slt{{i|iu}}"
// SEL-NOT: "riscv.slt{{i|iu}}"
// SEL-NOT: "riscv.slt{{u?}}"(%{{.*}}, %{{.*}})

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)}> ({
    %v0c = "llvm.mlir.constant"() <{value = -8 : i32}> : () -> i32
    %v0 = "llvm.freeze"(%v0c) : (i32) -> i32
    %k0 = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %p0 = "llvm.icmp"(%v0, %k0) <{predicate = 2 : i64}> : (i32, i32) -> i1
    %r0 = "llvm.zext"(%p0) : (i1) -> i64
    %v1c = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %v1 = "llvm.freeze"(%v1c) : (i32) -> i32
    %k1 = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %p1 = "llvm.icmp"(%v1, %k1) <{predicate = 2 : i64}> : (i32, i32) -> i1
    %r1 = "llvm.zext"(%p1) : (i1) -> i64
    %v2c = "llvm.mlir.constant"() <{value = -8 : i32}> : () -> i32
    %v2 = "llvm.freeze"(%v2c) : (i32) -> i32
    %k2 = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %p2 = "llvm.icmp"(%v2, %k2) <{predicate = 6 : i64}> : (i32, i32) -> i1
    %r2 = "llvm.zext"(%p2) : (i1) -> i64
    %v3c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %v3 = "llvm.freeze"(%v3c) : (i32) -> i32
    %k3 = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %p3 = "llvm.icmp"(%v3, %k3) <{predicate = 6 : i64}> : (i32, i32) -> i1
    %r3 = "llvm.zext"(%p3) : (i1) -> i64
    %v4c = "llvm.mlir.constant"() <{value = -6 : i32}> : () -> i32
    %v4 = "llvm.freeze"(%v4c) : (i32) -> i32
    %k4 = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %p4 = "llvm.icmp"(%v4, %k4) <{predicate = 9 : i64}> : (i32, i32) -> i1
    %r4 = "llvm.zext"(%p4) : (i1) -> i64
    %v5c = "llvm.mlir.constant"() <{value = -8 : i8}> : () -> i8
    %v5 = "llvm.freeze"(%v5c) : (i8) -> i8
    %k5 = "llvm.mlir.constant"() <{value = -7 : i8}> : () -> i8
    %p5 = "llvm.icmp"(%v5, %k5) <{predicate = 2 : i64}> : (i8, i8) -> i1
    %r5 = "llvm.zext"(%p5) : (i1) -> i64
    %v6c = "llvm.mlir.constant"() <{value = 100 : i8}> : () -> i8
    %v6 = "llvm.freeze"(%v6c) : (i8) -> i8
    %k6 = "llvm.mlir.constant"() <{value = -56 : i8}> : () -> i8
    %p6 = "llvm.icmp"(%v6, %k6) <{predicate = 6 : i64}> : (i8, i8) -> i1
    %r6 = "llvm.zext"(%p6) : (i1) -> i64
    %v7c = "llvm.mlir.constant"() <{value = -55 : i8}> : () -> i8
    %v7 = "llvm.freeze"(%v7c) : (i8) -> i8
    %k7 = "llvm.mlir.constant"() <{value = -56 : i8}> : () -> i8
    %p7 = "llvm.icmp"(%v7, %k7) <{predicate = 6 : i64}> : (i8, i8) -> i1
    %r7 = "llvm.zext"(%p7) : (i1) -> i64
    %v8c = "llvm.mlir.constant"() <{value = -56 : i8}> : () -> i8
    %v8 = "llvm.freeze"(%v8c) : (i8) -> i8
    %k8 = "llvm.mlir.constant"() <{value = -56 : i8}> : () -> i8
    %p8 = "llvm.icmp"(%v8, %k8) <{predicate = 7 : i64}> : (i8, i8) -> i1
    %r8 = "llvm.zext"(%p8) : (i1) -> i64
    %v9c = "llvm.mlir.constant"() <{value = 2047 : i16}> : () -> i16
    %v9 = "llvm.freeze"(%v9c) : (i16) -> i16
    %k9 = "llvm.mlir.constant"() <{value = 2046 : i16}> : () -> i16
    %p9 = "llvm.icmp"(%v9, %k9) <{predicate = 3 : i64}> : (i16, i16) -> i1
    %r9 = "llvm.zext"(%p9) : (i1) -> i64
    %v10c = "llvm.mlir.constant"() <{value = -2049 : i16}> : () -> i16
    %v10 = "llvm.freeze"(%v10c) : (i16) -> i16
    %k10 = "llvm.mlir.constant"() <{value = -2048 : i16}> : () -> i16
    %p10 = "llvm.icmp"(%v10, %k10) <{predicate = 5 : i64}> : (i16, i16) -> i1
    %r10 = "llvm.zext"(%p10) : (i1) -> i64
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5, %r6, %r7, %r8, %r9, %r10) : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000001#64, 0x0000000000000001#64, 0x0000000000000001#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000000#64]
