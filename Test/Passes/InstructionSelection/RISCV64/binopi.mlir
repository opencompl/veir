// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// imm12 binops select directly to their immediate form when the constant is on
// the right and fits a signed 12-bit field (PatGprSimm12<{add,or,and,xor}, ...>).
// The reg-reg fallback (out-of-range immediate, or constant on the left) is left
// for the generic isel-riscv64 pass, so here those stay as `llvm` ops.

"builtin.module"() ({
    // llvm.add x (const imm12) -> riscv.addi x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f0"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.add"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.addi"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.or x (const imm12) -> riscv.ori x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f1"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
        %r = "llvm.or"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.ori"(%{{.*}}) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.and x (const imm12) -> riscv.andi x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f2"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
        %r = "llvm.and"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.andi"(%{{.*}}) <{"value" = 6 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.xor x (const imm12) -> riscv.xori x imm
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f3"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = -2048 : i64}> : () -> i64
        %r = "llvm.xor"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.xori"(%{{.*}}) <{"value" = -2048 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Out-of-range immediate: not selected here (stays `llvm.add`).
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f4"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 2048 : i64}> : () -> i64
        %r = "llvm.add"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Constant on the left: not matched (mirrors PatGprImm's `(OpNode GPR, imm)`).
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f5"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.add"(%c, %a) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
