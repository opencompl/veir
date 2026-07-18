// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i128, i42) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i128, %b : i42):
        %sexta = "llvm.sext"(%a) : (i128) -> i256
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i128) -> i256
        %sextb = "llvm.sext"(%b) : (i42) -> i64
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i42) -> i64
        "test.test"(%sexta) : (i256) -> ()
        "test.test"(%sextb) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

