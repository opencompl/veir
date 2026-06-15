// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    // riscv.sll x (riscv.li imm) -> riscv.slli x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 1 : i64}>: () -> !riscv.reg
        %r = "riscv.sll"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r:%.*]] = "riscv.slli"([[a]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.srl x (riscv.li imm) -> riscv.srli x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a2:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 7 : i64}>: () -> !riscv.reg
        %r = "riscv.srl"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r2:%.*]] = "riscv.srli"([[a2]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r2]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.sra x (riscv.li imm) -> riscv.srai x imm  (max in-range 6-bit shamt)
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a3:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 63 : i64}>: () -> !riscv.reg
        %r = "riscv.sra"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r3:%.*]] = "riscv.srai"([[a3]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r3]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.ror x (riscv.li imm) -> riscv.rori x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a4:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 40 : i64}>: () -> !riscv.reg
        %r = "riscv.ror"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r4:%.*]] = "riscv.rori"([[a4]]) <{"value" = 40 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r4]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.bclr x (riscv.li imm) -> riscv.bclri x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a5:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 5 : i64}>: () -> !riscv.reg
        %r = "riscv.bclr"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r5:%.*]] = "riscv.bclri"([[a5]]) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r5]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.bext x (riscv.li imm) -> riscv.bexti x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a6:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 17 : i64}>: () -> !riscv.reg
        %r = "riscv.bext"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r6:%.*]] = "riscv.bexti"([[a6]]) <{"value" = 17 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r6]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.binv x (riscv.li imm) -> riscv.binvi x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a7:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 0 : i64}>: () -> !riscv.reg
        %r = "riscv.binv"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r7:%.*]] = "riscv.binvi"([[a7]]) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r7]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.bset x (riscv.li imm) -> riscv.bseti x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a8:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 62 : i64}>: () -> !riscv.reg
        %r = "riscv.bset"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r8:%.*]] = "riscv.bseti"([[a8]]) <{"value" = 62 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r8]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Non-commutative: li on the left is the shifted value, not the amount, so
    // riscv.sll (riscv.li imm) x must NOT fold.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a9:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 3 : i64}>: () -> !riscv.reg
        %r = "riscv.sll"(%c, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[v:%.*]] = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
        // CHECK:             [[r9:%.*]] = "riscv.sll"([[v]], [[a9]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r9]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Shift amount out of the unsigned 6-bit range (64): not folded.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a10:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 64 : i64}>: () -> !riscv.reg
        %r = "riscv.srl"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big:%.*]] = "riscv.li"() <{"value" = 64 : i64}> : () -> !riscv.reg
        // CHECK:             [[r10:%.*]] = "riscv.srl"([[a10]], [[big]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r10]]) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
