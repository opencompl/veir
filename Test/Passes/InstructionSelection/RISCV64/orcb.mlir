// RUN: veir-opt %s -p=isel-sdag-riscv64,isel-riscv64 | filecheck %s

// `sub (shl M (8 - Y)) (lshr M Y)`, where `M = and %z (0x0101_0101_0101_0101 <<< Y)`,
// fuses into `riscv.orcb M` (LLVM's combineSubShiftToOrcB). The `and` with the
// per-byte bit-`Y` mask is what makes the rewrite sound without known bits. Each
// function below should produce a `riscv.orcb` (so its `sub` was consumed, not
// lowered to `riscv.sub`); requiring four `riscv.orcb` results together forces all
// four shapes to fuse.

"builtin.module"() ({
    // Y = 0: right operand is `M` itself, left is `shl M 8`, mask 0x0101_0101_0101_0101.
    "func.func"()  <{function_type = (i64) -> (i64)}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.orcb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        "func.return"(%sub) : (i64) -> ()
    }) : () -> ()
    // Y = 3: left is `shl M 5`, right is `lshr M 3`, mask 0x0808_0808_0808_0808.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 578721382704613384 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c5 = "llvm.mlir.constant"() <{ "value" = 5 : i64 }> : () -> i64
        %c3 = "llvm.mlir.constant"() <{ "value" = 3 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c5) : (i64, i64) -> i64
        %srl = "llvm.lshr"(%m, %c3) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %srl) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.orcb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
    // Y = 7: left is `shl M 1`, right is `lshr M 7`, mask 0x8080_8080_8080_8080.
    // This is the top-bit-of-each-byte mask, whose i64 value is "negative"; it
    // exercises the signed/unsigned normalization in the matcher's mask check.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 9259542123273814144 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
        %c7 = "llvm.mlir.constant"() <{ "value" = 7 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c1) : (i64, i64) -> i64
        %srl = "llvm.lshr"(%m, %c7) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %srl) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.orcb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
    // Y = 0 with the mask on the left operand of the `and` (`and %mask %z`): the
    // matcher accepts the mask constant on either side.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m = "llvm.and"(%mask, %z) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.orcb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
