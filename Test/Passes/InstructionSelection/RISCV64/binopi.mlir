// RUN: veir-opt %s -p=riscv | filecheck %s

// imm12 binops select directly to their immediate form when the constant is on
// the right and fits a signed 12-bit field (PatGprSimm12<{add,or,and,xor}, ...>).
// An out-of-range immediate falls back to materializing the constant and the
// reg-reg form; a constant on the left is moved to the right by the
// post-legalizer combiner, so it still selects the immediate form.

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

    // Out-of-range immediate: materialized with `li`, then reg-reg `add`.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f4"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 2048 : i64}> : () -> i64
        %r = "llvm.add"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.li"() <{"value" = 2048 : i64}> : () -> !riscv.reg
        // CHECK:      %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Constant on the left: commuted to the right before selection, then `addi`.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f5"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %r = "llvm.add"(%c, %a) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.addi"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
