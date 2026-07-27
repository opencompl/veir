// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
        %one = "llvm.mlir.constant"() <{ "value" = 1 : i16 }> : () -> i16
        %two = "llvm.mlir.constant"() <{ "value" = 2 : i16 }> : () -> i16
        // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 1 : i16}> : () -> i16
        // CHECK-NEXT: %{{.*}} = "llvm.mlir.constant"() <{"value" = 2 : i16}> : () -> i16
        "test.test"(%one) : (i16) -> ()
        "test.test"(%two) : (i16) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
