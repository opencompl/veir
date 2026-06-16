// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    // riscv.or x (riscv.li imm) -> riscv.ori x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 7 : i64}>: () -> !riscv.reg
        %r = "riscv.or"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r:%.*]] = "riscv.ori"([[a]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.and x (riscv.li imm) -> riscv.andi x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a3:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 2047 : i64}>: () -> !riscv.reg
        %r = "riscv.and"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r3:%.*]] = "riscv.andi"([[a3]]) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r3]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.xor x (riscv.li imm) -> riscv.xori x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a4:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -2048 : i64}>: () -> !riscv.reg
        %r = "riscv.xor"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r4:%.*]] = "riscv.xori"([[a4]]) <{"value" = -2048 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r4]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.addw x (riscv.li imm) -> riscv.addiw x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a5:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 42 : i64}>: () -> !riscv.reg
        %r = "riscv.addw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r5:%.*]] = "riscv.addiw"([[a5]]) <{"value" = 42 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r5]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Out-of-range immediate: not folded (riscv.or stays as-is).
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a7:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 2048 : i64}>: () -> !riscv.reg
        %r = "riscv.or"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big:%.*]] = "riscv.li"() <{"value" = 2048 : i64}> : () -> !riscv.reg
        // CHECK:             [[r7:%.*]] = "riscv.or"([[a7]], [[big]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r7]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Out-of-range immediate: not folded (riscv.addw stays as-is).
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a8:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -2049 : i64}>: () -> !riscv.reg
        %r = "riscv.addw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big2:%.*]] = "riscv.li"() <{"value" = -2049 : i64}> : () -> !riscv.reg
        // CHECK:             [[r8:%.*]] = "riscv.addw"([[a8]], [[big2]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r8]]) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
