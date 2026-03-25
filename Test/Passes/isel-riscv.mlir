// RUN: veir-opt %s -p=globalisel-riscv | filecheck %s

"builtin.module"() ({
^bb0():
    %one = "llvm.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %two = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
    
    // CHECK:      %{{.*}} = "llvm.constant"() <{"value" = 1 : i32}> : () -> i32
    // CHECK-NEXT: %{{.*}} = "llvm.constant"() <{"value" = 2 : i32}> : () -> i32
    
    %add = "llvm.add"(%two, %one) : (i32, i32) -> i32

    // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64

}) : () -> ()
