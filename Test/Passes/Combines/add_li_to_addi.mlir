// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    // riscv.add x (riscv.li imm) -> riscv.addi x imm
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[arg:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = 1 : i64}>: () -> !riscv.reg
        %add = "riscv.add"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r:%.*]] = "riscv.addi"([[arg]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%add) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // riscv.add x (riscv.li imm) -> riscv.addi x imm  (lower bound of the field)
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[arg2:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -2048 : i64}>: () -> !riscv.reg
        %add = "riscv.add"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[r2:%.*]] = "riscv.addi"([[arg2]]) <{"value" = -2048 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%add) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r2]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // Immediate does not fit addi's signed 12-bit field: not folded.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[arg3:%.*]] : !riscv.reg):
        %c = "riscv.li"() <{"value" = -2049 : i64}>: () -> !riscv.reg
        %add = "riscv.add"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:             [[big:%.*]] = "riscv.li"() <{"value" = -2049 : i64}> : () -> !riscv.reg
        // CHECK:             [[r3:%.*]] = "riscv.add"([[arg3]], [[big]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%add) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r3]]) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
