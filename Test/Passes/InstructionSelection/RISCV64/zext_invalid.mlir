// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i128, i16) -> ()}> ({
    ^bb0(%a: i128, %b : i16):
        %zexta = "llvm.zext"(%a) : (i128) -> i256
        // CHECK:      %{{.*}} = "llvm.zext"(%{{.*}}) : (i128) -> i256
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

