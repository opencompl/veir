// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({

    // llvm.intr.smax -> riscv.max
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f0"}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.smax"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.max"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.smin -> riscv.min
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f1"}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.smin"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.min"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.umax -> riscv.maxu
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f2"}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.umax"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.maxu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // llvm.intr.umin -> riscv.minu
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f3"}> ({
    ^bb0(%a: i64, %b: i64):
        %r = "llvm.intr.umin"(%a, %b) : (i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.minu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // fshl with identical data operands is a rotate-left -> riscv.rol
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f4"}> ({
    ^bb0(%a: i64, %s: i64):
        %r = "llvm.intr.fshl"(%a, %a, %s) : (i64, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.rol"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // fshr with identical data operands is a rotate-right -> riscv.ror
    "func.func"()  <{function_type = (i64, i64) -> (), sym_name = "f5"}> ({
    ^bb0(%a: i64, %s: i64):
        %r = "llvm.intr.fshr"(%a, %a, %s) : (i64, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.ror"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 smax: sextw before max for correct signed comparison
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "f6"}> ({
    ^bb0(%a: i32, %b: i32):
        %r = "llvm.intr.smax"(%a, %b) : (i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.sextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.sextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.max"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 smin: sextw before min for correct signed comparison
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "f7"}> ({
    ^bb0(%a: i32, %b: i32):
        %r = "llvm.intr.smin"(%a, %b) : (i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.sextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.sextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.min"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 umax: zero-extended values work correctly with maxu
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "f8"}> ({
    ^bb0(%a: i32, %b: i32):
        %r = "llvm.intr.umax"(%a, %b) : (i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.maxu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 umin: zero-extended values work correctly with minu
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "f9"}> ({
    ^bb0(%a: i32, %b: i32):
        %r = "llvm.intr.umin"(%a, %b) : (i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.minu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 fshl (rotate-left) -> riscv.rolw
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "f10"}> ({
    ^bb0(%a: i32, %s: i32):
        %r = "llvm.intr.fshl"(%a, %a, %s) : (i32, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.rolw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32 fshr (rotate-right) -> riscv.rorw
    "func.func"()  <{function_type = (i32, i32) -> (), sym_name = "f11"}> ({
    ^bb0(%a: i32, %s: i32):
        %r = "llvm.intr.fshr"(%a, %a, %s) : (i32, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.rorw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
