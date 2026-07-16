// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i16) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i16, %b: i16):
        %add = "llvm.or"(%a, %b) : (i16, i16) -> i16
        // CHECK: %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) : (i16, i16) -> i16
        %add_disjoint = "llvm.or"(%a, %b) <{disjoint}>: (i16, i16) -> i16
        // CHECK-NEXT: %{{.*}} = "llvm.or"(%{{.*}}, %{{.*}}) <{disjoint}> : (i16, i16) -> i16
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
