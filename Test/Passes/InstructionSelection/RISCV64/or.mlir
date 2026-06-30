// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i64) -> ()}> ({
    ^bb0(%a: i64, %b: i64):
        %add = "llvm.or"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        %add_disjoint = "llvm.or"(%a, %b) <{disjoint}> : (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()

    "func.func"()  <{function_type = (i32, i32) -> ()}> ({
    ^bb(%a: i32, %b: i32):
        %or = "llvm.or"(%a, %b) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.or"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
