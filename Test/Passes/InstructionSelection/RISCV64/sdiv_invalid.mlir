// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i16) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i16, %b: i16):
        %sdiv = "llvm.sdiv"(%a, %b) : (i16, i16) -> i16
        // CHECK: %{{.*}} = "llvm.sdiv"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16

        "test.test"(%sdiv) : (i16) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
