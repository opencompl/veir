// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i32, %b: i32):
        %add = "llvm.or"(%a, %b) : (i32, i32) -> i32
        // CHECK: %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
        %add = "llvm.or"(%a, %b) <{disjoint}>: (i32, i32) -> i32
        // CHECK-NEXT: %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) <{disjoint}> : (i32, i32) -> i32
    }) : () -> ()
}) : () -> ()
