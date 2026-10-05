// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// Constants wider than a 64-bit register are not lowered.
"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
        %one = "llvm.mlir.constant"() <{ "value" = 1 : i65 }> : () -> i65
        %two = "llvm.mlir.constant"() <{ "value" = 2 : i65 }> : () -> i65
        // CHECK:      %{{.*}} = "llvm.mlir.constant"() <{"value" = 1 : i65}> : () -> i65
        // CHECK-NEXT: %{{.*}} = "llvm.mlir.constant"() <{"value" = 2 : i65}> : () -> i65
        "test.test"(%one) : (i65) -> ()
        "test.test"(%two) : (i65) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
