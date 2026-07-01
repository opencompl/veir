// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i16) -> ()}> ({
    ^bb0(%a: i16, %b: i16):
        %add = "llvm.mul"(%a, %b) : (i16, i16) -> i16
        // CHECK: %{{.*}} = "llvm.mul"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16

        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
