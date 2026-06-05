// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: !llvm.ptr):
        %val = "llvm.load"(%a) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !reg
        // CHECK-NEXT: {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!reg) -> !reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()
    
}) : () -> ()
