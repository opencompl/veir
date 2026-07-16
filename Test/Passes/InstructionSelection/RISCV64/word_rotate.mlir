// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// A constant-amount i32 rotate (funnel shift with identical data operands) selects
// to riscv.roriw. There is no `roliw`, so a rotate-left by C lowers to roriw with the
// negated immediate (32 - C) mod 32, mirroring `fshlConst` at i64. These fire only on
// i32 results; i64 rotates are left for the generic isel-riscv64 pass.

"builtin.module"() ({

    // fshr(a, a, 5) is rotate-right by 5 -> roriw a, 5
    "func.func"() <{function_type = (i32) -> (), sym_name = "f0"}> ({
    ^bb0(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
        %r = "llvm.intr.fshr"(%a, %a, %c) : (i32, i32, i32) -> i32
        // CHECK: %{{.*}} = "riscv.roriw"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // fshl(a, a, 5) is rotate-left by 5 == rotate-right by 27 -> roriw a, 27
    "func.func"() <{function_type = (i32) -> (), sym_name = "f1"}> ({
    ^bb0(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
        %l = "llvm.intr.fshl"(%a, %a, %c) : (i32, i32, i32) -> i32
        // CHECK: %{{.*}} = "riscv.roriw"(%{{.*}}) <{"value" = 27 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // A rotate by 0 stays a (no-op) rotate: fshl/fshr by 0 -> roriw a, 0
    "func.func"() <{function_type = (i32) -> (), sym_name = "f2"}> ({
    ^bb0(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
        %l = "llvm.intr.fshl"(%a, %a, %c) : (i32, i32, i32) -> i32
        %r = "llvm.intr.fshr"(%a, %a, %c) : (i32, i32, i32) -> i32
        // CHECK-COUNT-2: %{{.*}} = "riscv.roriw"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i64 rotate-left is not selected here (stays `llvm.intr.fshl` for isel-riscv64).
    "func.func"() <{function_type = (i64) -> (), sym_name = "f3"}> ({
    ^bb0(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %l = "llvm.intr.fshl"(%a, %a, %c) : (i64, i64, i64) -> i64
        // CHECK: %{{.*}} = "llvm.intr.fshl"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i64, i64) -> i64
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
