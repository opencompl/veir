// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.srli 63 (riscv.srai _ x) -> riscv.srli 63 x` (and the `i32` analogue at
// bit 31): an arithmetic right shift never changes the top bit, so a following
// logical shift by (width - 1), which keeps only that bit, doesn't care what the
// inner `srai`/`sraiw`'s own shift amount was. Mirrors LLVM's generic (division-
// agnostic) `DAGCombiner::visitSRL` rule `fold (srl (sra X, Y), 31) -> (srl X, 31)`.

"builtin.module"() ({
    // riscv.srli 63 (riscv.srai 5 x) -> riscv.srli 63 x: the inner shift amount is
    // discarded, and only the outer `srli 63` (renamed here, since a new op is
    // created) survives.
    "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%x: !riscv.reg):
        %sra = "riscv.srai"(%x) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        %srl = "riscv.srli"(%sra) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:      %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: "func.return"(%{{.*}}) : (!riscv.reg) -> ()
        "func.return"(%srl) : (!riscv.reg) -> ()
    }) : () -> ()

    // i32 analogue: riscv.srliw 31 (riscv.sraiw 7 x) -> riscv.srliw 31 x.
    "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%x: !riscv.reg):
        %sraw = "riscv.sraiw"(%x) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
        %srlw = "riscv.srliw"(%sraw) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:      %{{.*}} = "riscv.srliw"(%{{.*}}) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: "func.return"(%{{.*}}) : (!riscv.reg) -> ()
        "func.return"(%srlw) : (!riscv.reg) -> ()
    }) : () -> ()

    // Outer shift amount not (width - 1): the pattern must not fire, so both
    // instructions survive.
    "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%x: !riscv.reg):
        %sra = "riscv.srai"(%x) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        %srl = "riscv.srli"(%sra) <{"value" = 62 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:      %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 62 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%srl) : (!riscv.reg) -> ()
    }) : () -> ()

    // No inner `srai`: not matched, `riscv.srli` is left as-is.
    "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
    ^bb(%x: !riscv.reg):
        %srl = "riscv.srli"(%x) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:      %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%srl) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()
