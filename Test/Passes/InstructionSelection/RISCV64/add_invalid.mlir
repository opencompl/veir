// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb(%a: i32, %b: i32):
        %add = "llvm.add"(%a, %b) : (i32, i32) -> i32
        // CHECK: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    }) : () -> ()
}) : () -> ()
