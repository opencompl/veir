// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb(%a : !reg):
        %c0 = "riscv.li"() <{"value" = 0 : i64}>: () -> !reg
        %add = "riscv.add"(%a, %c0) : (!reg, !reg) -> !reg
        "riscv.return"(%add) : (!reg) -> ()
    }) : () -> ()
}) : () -> ()
