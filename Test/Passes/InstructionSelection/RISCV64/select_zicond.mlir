// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({

    // select c, t, 0 -> riscv.czeroeqz t, c
    "func.func"()  <{function_type = (i1, i64) -> (), sym_name = "f0"}> ({
    ^bb0(%c: i1, %t: i64):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64
        %r = "llvm.select"(%c, %t, %zero) : (i1, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // select c, 0, f -> riscv.czeronez f, c
    "func.func"()  <{function_type = (i1, i64) -> (), sym_name = "f1"}> ({
    ^bb0(%c: i1, %f: i64):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64
        %r = "llvm.select"(%c, %zero, %f) : (i1, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // general select c, t, f -> or (czero.eqz t, c) (czero.nez f, c)
    "func.func"()  <{function_type = (i1, i64, i64) -> (), sym_name = "f2"}> ({
    ^bb0(%c: i1, %t: i64, %f: i64):
        %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // i32: select c, t, 0 -> riscv.czeroeqz t, c
    "func.func"()  <{function_type = (i1, i32) -> (), sym_name = "f3"}> ({
    ^bb0(%c: i1, %t: i32):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
        %r = "llvm.select"(%c, %t, %zero) : (i1, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // i32: select c, 0, f -> riscv.czeronez f, c
    "func.func"()  <{function_type = (i1, i32) -> (), sym_name = "f4"}> ({
    ^bb0(%c: i1, %f: i32):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
        %r = "llvm.select"(%c, %zero, %f) : (i1, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // i32: general select
    "func.func"()  <{function_type = (i1, i32, i32) -> (), sym_name = "f5"}> ({
    ^bb0(%c: i1, %t: i32, %f: i32):
        %r = "llvm.select"(%c, %t, %f) : (i1, i32, i32) -> i32
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
    // i1: general select
    "func.func"()  <{function_type = (i1, i1, i1) -> (), sym_name = "f6"}> ({
    ^bb0(%c: i1, %t: i1, %f: i1):
        %r = "llvm.select"(%c, %t, %f) : (i1, i1, i1) -> i1
        // CHECK-DAG: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.czeronez"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-DAG: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "test.test"(%r) : (i1) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // i16: select c, t, 0 -> riscv.czeroeqz t, c
    "func.func"()  <{function_type = (i1, i16) -> (), sym_name = "f7"}> ({
    ^bb0(%c: i1, %t: i16):
        %zero = "llvm.mlir.constant"() <{ "value" = 0 : i16 }> : () -> i16
        %r = "llvm.select"(%c, %t, %zero) : (i1, i16, i16) -> i16
        // CHECK-LABEL: @f7(
        // CHECK-NOT: "riscv.or"
        // CHECK: %{{.*}} = "riscv.czeroeqz"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NOT: "riscv.or"
        "test.test"(%r) : (i16) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // A comparison is already zero or one, so the condition is not masked.
    "func.func"()  <{function_type = (i64, i64, i64, i64) -> (), sym_name = "f8"}> ({
    ^bb0(%a: i64, %b: i64, %t: i64, %f: i64):
        %c = "llvm.icmp"(%a, %b) <{predicate = 2 : i64}> : (i64, i64) -> i1
        %r = "llvm.select"(%c, %t, %f) : (i1, i64, i64) -> i64
        // CHECK-LABEL: @f8(
        // CHECK-NOT: "riscv.andi"
        // CHECK: %[[C:.*]] = "riscv.slt"
        // CHECK-NOT: "riscv.andi"
        // CHECK-DAG: "riscv.czeroeqz"(%{{.*}}, %[[C]])
        // CHECK-DAG: "riscv.czeronez"(%{{.*}}, %[[C]])
        "test.test"(%r) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
