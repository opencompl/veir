// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    // riscv.slt x (riscv.li imm) -> riscv.slti x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 7 : i64}>: () -> !riscv.reg
        %r = "riscv.slt"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r:%.*]] = "riscv.slti"([[a]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.sltu x (riscv.li imm) -> riscv.sltiu x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a2:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 2047 : i64}>: () -> !riscv.reg
        %r = "riscv.sltu"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r2:%.*]] = "riscv.sltiu"([[a2]]) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r2]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.slt x (riscv.li imm) -> riscv.slti x imm  (min in-range immediate)
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a3:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -2048 : i64}>: () -> !riscv.reg
        %r = "riscv.slt"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r3:%.*]] = "riscv.slti"([[a3]]) <{"value" = -2048 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r3]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Non-commutative: li on the left is the lower bound, not rs1. For unsigned
    // there is no profitable set-greater-than-immediate fold, so riscv.sltu
    // (riscv.li imm) x must NOT fold.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a4:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 4 : i64}>: () -> !riscv.reg
        %r = "riscv.sltu"(%c, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[v:%.*]] = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
        // CHECK:             [[r4:%.*]] = "riscv.sltu"([[v]], [[a4]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r4]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Out-of-range immediate: not folded (riscv.slt stays as-is).
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a5:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 2048 : i64}>: () -> !riscv.reg
        %r = "riscv.slt"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big:%.*]] = "riscv.li"() <{"value" = 2048 : i64}> : () -> !riscv.reg
        // CHECK:             [[r5:%.*]] = "riscv.slt"([[a5]], [[big]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r5]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Out-of-range immediate: not folded (riscv.sltu stays as-is).
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a6:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -2049 : i64}>: () -> !riscv.reg
        %r = "riscv.sltu"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big2:%.*]] = "riscv.li"() <{"value" = -2049 : i64}> : () -> !riscv.reg
        // CHECK:             [[r6:%.*]] = "riscv.sltu"([[a6]], [[big2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r6]]) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
