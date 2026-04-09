// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i128, %b : i16):
        %zexta = "llvm.zext"(%a) : (i128) -> i16
        // CHECK:      %{{.*}} = "llvm.zext"(%{{.*}}) : (i128) -> i16
        %zextb = "llvm.zext"(%b) : (i16) -> i8
        // CHECK:      %{{.*}} = "llvm.zext"(%{{.*}}) : (i16) -> i8
    }) : () -> ()
}) : () -> ()

