// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb(%a: i64, %b: i64):
        %add = "llvm.ashr"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sra"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        "test.test"(%add) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    "func.func"()  <{function_type = (i32, i32) -> ()}> ({
    ^bb(%a: i32, %b: i32):
        %ashr32 = "llvm.ashr"(%a, %b) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sraw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        "test.test"(%ashr32) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    "func.func"()  <{function_type = (i8, i8) -> ()}> ({
    ^bb(%a: i8, %b: i8):
        %ashr8 = "llvm.ashr"(%a, %b) : (i8, i8) -> i8
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sextb"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sra"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i8
        "test.test"(%ashr8) : (i8) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
