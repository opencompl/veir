// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    // riscv.slli (riscv.zextw x) shamt -> riscv.slliuw x shamt
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a:%.*]] : !riscv.reg):
        %z = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
        %r = "riscv.slli"(%z) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:             [[r:%.*]] = "riscv.slliuw"([[a]]) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r]]) : (!riscv.reg) -> ()
    }) : () -> ()

    // A plain riscv.slli (operand not a zextw) must NOT fold.
    "func.func"()  <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[a2:%.*]] : !riscv.reg):
        %r = "riscv.slli"(%a) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:             [[r2:%.*]] = "riscv.slli"([[a2]]) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (!riscv.reg) -> ()
        // CHECK:             "func.return"([[r2]]) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
