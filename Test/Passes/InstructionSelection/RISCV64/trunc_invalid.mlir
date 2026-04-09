// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i128, %b : i16):
        %trunca = "llvm.trunc"(%a) : (i128) -> i16
        // CHECK:      %{{.*}} = "llvm.trunc"(%{{.*}}) : (i128) -> i16
        %truncb = "llvm.trunc"(%b) : (i16) -> i32
        // CHECK:      %{{.*}} = "llvm.trunc"(%{{.*}}) : (i16) -> i32
    }) : () -> ()
}) : () -> ()

