// RUN: veir-opt %s -p=isel-sdag-riscv64,riscv-combine | filecheck %s

// `sdiv x, 2` is the one power-of-two divisor where `sdivPow2`'s general
// 4-instruction sequence shrinks to 3: the correction shift's amount `W - k`
// coincides with `W - 1` exactly when `k = 1`, so `riscv-combine`'s
// `srl_sra_signbit` folds away the sign-splat `srai`. This matches LLVM's actual
// `llc` output for `sdiv i64/i32 %a, 2` (and is *not* a `k = 1` special case in
// `sdivPow2` itself; the negative-divisor and non-eligible-`k` cases are covered
// directly in `riscv_combine_srl_sra_signbit.mlir`).

"builtin.module"() ({
    // llvm.sdiv x, 2 -> riscv.srli 63 x / riscv.add x _ / riscv.srai 1 _
    // (no `riscv.srai 63` sign-splat survives).
    "func.func"() <{function_type = (i64) -> i64}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
        %r = "llvm.sdiv"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT:  "riscv.srai"(%{{.*}}) <{"value" = 63 : i64}>
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // i32 analogue: riscv.srliw 31 x / riscv.addw x _ / riscv.sraiw 1 _.
    "func.func"() <{function_type = (i32) -> i32}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
        %r = "llvm.sdiv"(%a, %c) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "riscv.srliw"(%{{.*}}) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.addw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sraiw"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NOT:  "riscv.sraiw"(%{{.*}}) <{"value" = 31 : i64}>
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
