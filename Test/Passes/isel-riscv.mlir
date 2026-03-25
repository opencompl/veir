// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
^bb0():
    %one = "llvm.constant"() <{ "value" = 1 : i64 }> : () -> i64
    %two = "llvm.constant"() <{ "value" = 2 : i64 }> : () -> i64
    // CHECK:      %{{.*}} = "llvm.constant"() <{"value" = 1 : i64}> : () -> i64
    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 2 : i64}> : () -> i64
    
    %add = "llvm.add"(%one, %two) : (i64, i64) -> i64
    // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
    
    %one = "llvm.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %two = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
    // CHECK:      %{{.*}} = "llvm.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 2 : i32}> : () -> i32
    
    %add = "llvm.add"(%one, %two) : (i32, i32) -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32

}) : () -> ()
