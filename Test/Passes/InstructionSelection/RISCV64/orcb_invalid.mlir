// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// None of these should fuse into `riscv.orcb`: each violates one of the matcher's
// guards, so the `sub` must lower normally to `riscv.sub`. The `CHECK-NOT`s
// interleaved with the per-function `CHECK`s assert no `riscv.orcb` appears
// anywhere in the output.

// CHECK-NOT: "riscv.orcb"

"builtin.module"() ({
    // Wrong mask: `2` is not a per-byte bit-`Y` mask, so a byte of `M` could have
    // a bit other than bit 0 set and `(M << 8) - M` is not `orc.b M`.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "test.test"(%sub) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    // No `and` at all: the shifted value is a bare argument, so the soundness gate
    // has nothing to prove each byte has only bit `Y` set. (Unsound to fuse.)
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%z, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %z) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "test.test"(%sub) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    // Shift-amount mismatch: mask is for Y=3 and `shl` is by 5 (Y=3), but `lshr`
    // is by 2 instead of 3.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 578721382704613384 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c5 = "llvm.mlir.constant"() <{ "value" = 5 : i64 }> : () -> i64
        %c2 = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c5) : (i64, i64) -> i64
        %srl = "llvm.lshr"(%m, %c2) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %srl) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "test.test"(%sub) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    // Mask/shift inconsistency: shifts say Y=3 (`shl` 5, `lshr` 3) but the mask is
    // the Y=0 mask `0x0101_0101_0101_0101` rather than `0x0808_0808_0808_0808`.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c5 = "llvm.mlir.constant"() <{ "value" = 5 : i64 }> : () -> i64
        %c3 = "llvm.mlir.constant"() <{ "value" = 3 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c5) : (i64, i64) -> i64
        %srl = "llvm.lshr"(%m, %c3) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %srl) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "test.test"(%sub) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    // Different masked values: the `shl` operand and the right operand are distinct
    // `and` results, so they are not the same `M`.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m1 = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %m2 = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m1, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m2) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "test.test"(%sub) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    // Out-of-range left shift: `shl` by 9 gives Y = 8 - 9 < 0, outside `0 ≤ Y < 8`.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c9 = "llvm.mlir.constant"() <{ "value" = 9 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c9) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "test.test"(%sub) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
