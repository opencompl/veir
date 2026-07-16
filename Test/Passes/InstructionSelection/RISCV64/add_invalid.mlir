// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i16) -> (), sym_name = "foo"}> ({
    ^bb(%a: i16, %b: i16):
        %add = "llvm.add"(%a, %b) : (i16, i16) -> i16
        // CHECK: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
