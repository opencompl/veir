// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i32, %b: i32):
        %urem = "llvm.urem"(%a, %b) : (i32, i32) -> i32
        // CHECK: %{{.*}} = "llvm.urem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32

    }) : () -> ()
}) : () -> ()
