// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i128, i16) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i128, %b : i42):
        %zexta = "llvm.zext"(%a) : (i128) -> i256
        // CHECK:      %{{.*}} = "llvm.zext"(%{{.*}}) : (i128) -> i256
        %zextb = "llvm.zext"(%b) : (i42) -> i64
        // CHECK:      %{{.*}} = "llvm.zext"(%{{.*}}) : (i42) -> i64
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

