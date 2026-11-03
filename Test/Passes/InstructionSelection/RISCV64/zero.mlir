// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
        %null = "llvm.mlir.zero"() : () -> !llvm.ptr
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> !llvm.ptr
        %i1 = "llvm.mlir.zero"() : () -> i1
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i1
        %i64 = "llvm.mlir.zero"() : () -> i64
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i64
        %i128 = "llvm.mlir.zero"() : () -> i128
        // CHECK: %{{.*}} = "llvm.mlir.zero"() : () -> i128
        "test.test"(%null) : (!llvm.ptr) -> ()
        "test.test"(%i1) : (i1) -> ()
        "test.test"(%i64) : (i64) -> ()
        "test.test"(%i128) : (i128) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
