// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = () -> ()}> ({
        %one = "llvm.mlir.poison"() : () -> i64
        %two = "llvm.mlir.poison"() : () -> i32
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.mlir.poison"() : () -> i32
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
