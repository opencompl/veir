// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i64, %b: i64):
        %sub = "llvm.sub"(%a, %b) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64
        %sub_nsw = "llvm.sub"(%a, %b) <{"overflowFlags" = 1 : i32}> : (i64, i64) -> i64
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64
        %sub_nuw = "llvm.sub"(%a, %b) <{"overflowFlags" = 2 : i32}> : (i64, i64) -> i64
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64
        %sub_nuw_nsw = "llvm.sub"(%a, %b) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
        // CHECK-NEXT:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64
    
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
