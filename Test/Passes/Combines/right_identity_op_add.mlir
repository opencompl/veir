// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
    ^bb(%a : !riscv.reg):
        // CHECK:             ^{{.*}}([[arg:%.*]] : !riscv.reg):
        %c0 = "riscv.li"() <{"value" = 0 : i64}>: () -> !riscv.reg
        %add = "riscv.add"(%a, %c0) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // The remaining value is unused and can be eliminated by DCE.
        // CHECK-NEXT:       [[zero:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        %c1 = "riscv.li"() <{"value" = 1 : i64}>: () -> !riscv.reg
        %add1 = "riscv.add"(%a, %c1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT:       [[one:%.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT:       %{{.*}} =  "riscv.add"([[arg]], [[one]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
