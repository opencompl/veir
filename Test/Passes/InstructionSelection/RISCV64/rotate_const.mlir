// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A rotate (funnel shift with identical data operands) by a constant amount
// selects to riscv.rori. There is no `roli`, so a rotate-left by C lowers to
// rori with the negated immediate (64 - C) mod 64, mirroring LLVM.

"builtin.module"() ({

    // fshr(a, a, 5) is rotate-right by 5 -> rori a, 5
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%a: i64):
        %c = "llvm.mlir.constant"() <{ "value" = 5 : i64 }> : () -> i64
        %r = "llvm.intr.fshr"(%a, %a, %c) : (i64, i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.rori"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // fshl(a, a, 5) is rotate-left by 5 == rotate-right by 59 -> rori a, 59
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%a: i64):
        %c = "llvm.mlir.constant"() <{ "value" = 5 : i64 }> : () -> i64
        %l = "llvm.intr.fshl"(%a, %a, %c) : (i64, i64, i64) -> i64
        // CHECK: %{{.*}} = "riscv.rori"(%{{.*}}) <{"value" = 59 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // A rotate by 0 stays a (no-op) rotate: fshl/fshr by 0 -> rori a, 0
    "func.func"()  <{function_type = (i64) -> ()}> ({
    ^bb0(%a: i64):
        %c = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64
        %l = "llvm.intr.fshl"(%a, %a, %c) : (i64, i64, i64) -> i64
        %r = "llvm.intr.fshr"(%a, %a, %c) : (i64, i64, i64) -> i64
        // CHECK-COUNT-2: %{{.*}} = "riscv.rori"(%{{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
