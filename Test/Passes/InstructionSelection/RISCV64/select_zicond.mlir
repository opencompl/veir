// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({

    // select c, t, 0 -> riscv.czeroeqz t, c
    "func.func"()  <{function_type = (i1, i64) -> ()}> ({
    ^bb0(%c: i1, %t: i64):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64
        %r = "llvm.select"(%c, %t, %zero) : (i1, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // select c, 0, f -> riscv.czeronez f, c
    "func.func"()  <{function_type = (i1, i64) -> ()}> ({
    ^bb0(%c: i1, %f: i64):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64
        %r = "llvm.select"(%c, %zero, %f) : (i1, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // general select c, t, f -> or (czero.eqz t, c) (czero.nez f, c)
    "func.func"()  <{function_type = (i1, i64, i64) -> ()}> ({
    ^bb0(%c: i1, %t: i64, %f: i64):
        %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32: select c, t, 0 -> riscv.czeroeqz t, c
    "func.func"()  <{function_type = (i1, i32) -> ()}> ({
    ^bb0(%c: i1, %t: i32):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
        %r = "llvm.select"(%c, %t, %zero) : (i1, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32: select c, 0, f -> riscv.czeronez f, c
    "func.func"()  <{function_type = (i1, i32) -> ()}> ({
    ^bb0(%c: i1, %f: i32):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
        %r = "llvm.select"(%c, %zero, %f) : (i1, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

    // i32: general select
    "func.func"()  <{function_type = (i1, i32, i32) -> ()}> ({
    ^bb0(%c: i1, %t: i32, %f: i32):
        %r = "llvm.select"(%c, %t, %f) : (i1, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
