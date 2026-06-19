// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i128, i42, i8) -> ()}> ({
    ^bb0(%a: i128, %b : i42, %c: i8):
        %sexta = "llvm.sext"(%a) : (i128) -> i256
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i128) -> i256
        %sextb = "llvm.sext"(%b) : (i42) -> i64
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i42) -> i64
        %sextc = "llvm.sext"(%c) : (i8) -> i64
        // CHECK:      %{{.*}} = "llvm.sext"(%{{.*}}) : (i8) -> i64
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

