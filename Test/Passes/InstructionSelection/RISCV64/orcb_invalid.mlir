// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// When the mask is not the per-byte bit-0 mask `0x0101_0101_0101_0101`, the
// soundness gate fails: a byte of `M` could have a bit other than bit 0 set, so
// `(M << 8) - M` is not `orc.b M`. The `sub` must lower normally to `riscv.sub`.

"builtin.module"() ({
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%z: i64):
        %mask = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
        %m = "llvm.and"(%z, %mask) : (i64, i64) -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
        %shl = "llvm.shl"(%m, %c8) : (i64, i64) -> i64
        %sub = "llvm.sub"(%shl, %m) : (i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.orcb"
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
