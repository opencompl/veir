// RUN: veir-opt %s -p=isel-sdag-riscv64,isel-riscv64 | filecheck %s

// LLVM models `not y` as `xor y -1`. The Zbb logic-with-negate forms fuse a
// `not` feeding an `and`/`or`/`xor` into a single instruction (mirroring LLVM's
// TableGen patterns `(and X, (not Y)) -> ANDN`, etc.). These run in the SDAG
// pass, before the bulk per-op lowering would otherwise consume the `not` and
// the logic op separately. Each function should produce the fused op.

"builtin.module"() ({
    // and x (not y) -> riscv.andn
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%x: i64, %y: i64):
        %ones = "llvm.mlir.constant"() <{ "value" = -1 : i64 }> : () -> i64
        %not = "llvm.xor"(%y, %ones) : (i64, i64) -> i64
        %r = "llvm.and"(%x, %not) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.andn"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
    // or x (not y) -> riscv.orn
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%x: i64, %y: i64):
        %ones = "llvm.mlir.constant"() <{ "value" = -1 : i64 }> : () -> i64
        %not = "llvm.xor"(%y, %ones) : (i64, i64) -> i64
        %r = "llvm.or"(%x, %not) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.orn"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
    // xor x (not y) -> riscv.xnor  (i.e. ~(x ^ y))
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%x: i64, %y: i64):
        %ones = "llvm.mlir.constant"() <{ "value" = -1 : i64 }> : () -> i64
        %not = "llvm.xor"(%y, %ones) : (i64, i64) -> i64
        %r = "llvm.xor"(%x, %not) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.xnor"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
    // The `not` is accepted on either operand: and (not y) x -> riscv.andn
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%x: i64, %y: i64):
        %ones = "llvm.mlir.constant"() <{ "value" = -1 : i64 }> : () -> i64
        %not = "llvm.xor"(%y, %ones) : (i64, i64) -> i64
        %r = "llvm.and"(%not, %x) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.andn"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
