// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    // riscv.sllw x (riscv.li imm) -> riscv.slliw x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 1 : i64}>: () -> !riscv.reg
        %r = "riscv.sllw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r:%.*]] = "riscv.slliw"([[a]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.srlw x (riscv.li imm) -> riscv.srliw x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a2:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 7 : i64}>: () -> !riscv.reg
        %r = "riscv.srlw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r2:%.*]] = "riscv.srliw"([[a2]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r2]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.sraw x (riscv.li imm) -> riscv.sraiw x imm  (max in-range shamt)
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a3:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 31 : i64}>: () -> !riscv.reg
        %r = "riscv.sraw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r3:%.*]] = "riscv.sraiw"([[a3]]) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r3]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.rorw x (riscv.li imm) -> riscv.roriw x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a4:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 12 : i64}>: () -> !riscv.reg
        %r = "riscv.rorw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r4:%.*]] = "riscv.roriw"([[a4]]) <{"value" = 12 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r4]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Non-commutative: li on the left is the shifted value, not the amount, so
    // riscv.sllw (riscv.li imm) x must NOT fold.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a5:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 4 : i64}>: () -> !riscv.reg
        %r = "riscv.sllw"(%c, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[v:%.*]] = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
        // CHECK:             [[r5:%.*]] = "riscv.sllw"([[v]], [[a5]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r5]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Shift amount out of the unsigned 5-bit range (32): not folded.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a6:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 32 : i64}>: () -> !riscv.reg
        %r = "riscv.srlw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big:%.*]] = "riscv.li"() <{"value" = 32 : i64}> : () -> !riscv.reg
        // CHECK:             [[r6:%.*]] = "riscv.srlw"([[a6]], [[big]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r6]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Negative shift amount (-1): not folded.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a7:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -1 : i64}>: () -> !riscv.reg
        %r = "riscv.sraw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[neg:%.*]] = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
        // CHECK:             [[r7:%.*]] = "riscv.sraw"([[a7]], [[neg]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r7]]) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
