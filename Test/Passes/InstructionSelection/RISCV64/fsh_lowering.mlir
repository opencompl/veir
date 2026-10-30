// RUN: veir-opt %s -p=riscv > %t
// RUN: not grep -E '"(gmir\.|llvm\.intr\.fsh)' %t

// Each funnel-shift and rotate lowering path is taken, and nothing is left unlowered. The
// lowerings are proved correct in `Veir.Passes.Legalization.Proofs`.

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "f"}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %x1 = "llvm.trunc"(%a) : (i64) -> i1
    %y1 = "llvm.trunc"(%b) : (i64) -> i1
    %z1 = "llvm.trunc"(%c) : (i64) -> i1
    %x5 = "llvm.trunc"(%a) : (i64) -> i5
    %z5 = "llvm.trunc"(%c) : (i64) -> i5
    %x8 = "llvm.trunc"(%a) : (i64) -> i8
    %y8 = "llvm.trunc"(%b) : (i64) -> i8
    %z8 = "llvm.trunc"(%c) : (i64) -> i8
    %x24 = "llvm.trunc"(%a) : (i64) -> i24
    %y24 = "llvm.trunc"(%b) : (i64) -> i24
    %z24 = "llvm.trunc"(%c) : (i64) -> i24
    %c3 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    // Width one, power-of-two width, other width, constant amount.
    %r1 = "llvm.intr.fshl"(%x1, %y1, %z1) : (i1, i1, i1) -> i1
    %r2 = "llvm.intr.fshl"(%x8, %y8, %z8) : (i8, i8, i8) -> i8
    %r3 = "llvm.intr.fshr"(%x24, %y24, %z24) : (i24, i24, i24) -> i24
    %r4 = "llvm.intr.fshr"(%x8, %y8, %c3) : (i8, i8, i8) -> i8
    // Rotates of a power-of-two width and of another width.
    %r5 = "llvm.intr.fshl"(%x8, %x8, %z8) : (i8, i8, i8) -> i8
    %r6 = "llvm.intr.fshr"(%x5, %x5, %z5) : (i5, i5, i5) -> i5
    %e1 = "llvm.zext"(%r1) : (i1) -> i64
    %e2 = "llvm.zext"(%r2) : (i8) -> i64
    %e3 = "llvm.zext"(%r3) : (i24) -> i64
    %e4 = "llvm.zext"(%r4) : (i8) -> i64
    %e5 = "llvm.zext"(%r5) : (i8) -> i64
    %e6 = "llvm.zext"(%r6) : (i5) -> i64
    "test.test"(%e1, %e2, %e3, %e4, %e5, %e6) : (i64, i64, i64, i64, i64, i64) -> ()
    "func.return"(%e1) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
