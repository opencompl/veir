// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
        %one = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
        %two = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i64
        // CHECK-NEXT: [[B:%.*]] = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[B]]) : (!riscv.reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()

    "func.func"()  <{function_type = () -> (), sym_name = "bar"}> ({
        %one = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
        // CHECK: [[C:%.*]] = "riscv.li"() <{"value" = 1 : i32}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[C]]) : (!riscv.reg) -> i32
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
