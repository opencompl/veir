// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb(%a : !reg):
        // CHECK:             ^{{.*}}([[arg:%.*]] : !reg):
        %c0 = "riscv.li"() <{"value" = 0 : i64}>: () -> !reg
        %add = "riscv.add"(%a, %c0) : (!reg, !reg) -> !reg
        // The remaining value is unused and can be eliminated by DCE.
        // CHECK-NEXT:       [[zero:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !reg
        %c1 = "riscv.li"() <{"value" = 1 : i64}>: () -> !reg
        %add1 = "riscv.add"(%a, %c1) : (!reg, !reg) -> !reg
        // CHECK-NEXT:       [[one:%.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !reg
        // CHECK-NEXT:       %{{.*}} =  "riscv.add"([[arg]], [[one]]) : (!reg, !reg) -> !reg
    }) : () -> ()
}) : () -> ()
