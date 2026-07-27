// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i16) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i16, %b: i16):
        %add = "llvm.sub"(%a, %b) : (i16, i16) -> i16
        // CHECK: %{{.*}} = "llvm.sub"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16

        "test.test"(%add) : (i16) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
