// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// `sub (shl M (8 - Y)) (lshr M Y)`, where `M = and %z (0x0101_0101_0101_0101 <<< Y)`,
// fuses into `riscv.orcb M` (LLVM's combineSubShiftToOrcB). The `and` with the
// per-byte bit-`Y` mask is what makes the rewrite sound without known bits. Neither
// function should lower its `sub` to a `riscv.sub`.
// CHECK-NOT: "riscv.sub"

"builtin.module"() ({
    // Y = 0: right operand is `M` itself, left is `shl M 8`, mask 0x0101_0101_0101_0101.
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.orcb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
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
}) : () -> ()
