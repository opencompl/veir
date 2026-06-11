// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// `sub (shl M 8) M`, where `M = and %z 0x0101_0101_0101_0101`, fuses into
// `riscv.orcb M` (the Y=0 case of LLVM's combineSubShiftToOrcB). The `and` with
// the per-byte bit-0 mask is what makes the rewrite sound without known bits.

"builtin.module"() ({
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 72340172838076673 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // The masked value is preserved as a `riscv.and`, and the `sub` is fused
        // into a `riscv.orcb` instead of a `riscv.sub`.
        // CHECK-DAG: %{{.*}} = "riscv.and"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.orcb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.sub"
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
