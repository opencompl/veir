// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i128, i16) -> ()}> ({
    ^bb0(%a: i128, %b : i16):
        %sexta = "llvm.sext"(%a) : (i128) -> i256
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i128) -> i256
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

