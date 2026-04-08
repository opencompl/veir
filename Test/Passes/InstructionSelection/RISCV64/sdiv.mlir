// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i64, %b: i64):
        %sdiv = "llvm.sdiv"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.div"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64
        
    ^bb1(%a: i64, %b: i64):
        %sdiv = "llvm.sdiv"(%a, %b) <{exact}> : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.div"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64

    }) : () -> ()
}) : () -> ()
