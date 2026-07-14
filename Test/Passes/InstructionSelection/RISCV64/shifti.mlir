// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// Shifts by a constant in [0, 63] select to their immediate form
// (PatGprUimmLog2XLen<{shl,srl,sra}, ...>).

"builtin.module"() ({
    // llvm.shl x (const) -> riscv.slli x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f0"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.shl"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.slli"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.lshr x (const) -> riscv.srli x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f1"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
        %r = "llvm.lshr"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.ashr x (const) -> riscv.srai x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f2"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %r = "llvm.ashr"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Shift amount out of [0,63]: not selected here (stays `llvm.shl`).
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f3"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
        %r = "llvm.shl"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "llvm.shl"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
