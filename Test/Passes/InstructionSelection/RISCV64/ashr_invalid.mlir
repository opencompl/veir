// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb(%a: i32, %b: i32):
        %add = "llvm.ashr"(%a, %b) : (i32, i32) -> i32
        // CHECK:      %{{.*}} = "llvm.ashr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    }) : () -> ()
}) : () -> ()
