// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i128, %b : i16):
        %sexta = "llvm.sext"(%a) : (i128) -> i16
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i128) -> i16
        %sextb = "llvm.sext"(%b) : (i16) -> i8
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i16) -> i8
    }) : () -> ()
}) : () -> ()

