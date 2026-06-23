// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({

    // llvm.intr.smax -> riscv.max
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.smax"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.max"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.smin -> riscv.min
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.smin"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.min"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.umax -> riscv.maxu
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.umax"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.maxu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.umin -> riscv.minu
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.umin"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.minu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // fshl with identical data operands is a rotate-left -> riscv.rol
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %s: i64):
        %r = "llvm.intr.fshl"(%a, %a, %s) : (i64, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.rol"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // fshr with identical data operands is a rotate-right -> riscv.ror
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %s: i64):
        %r = "llvm.intr.fshr"(%a, %a, %s) : (i64, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.ror"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
