// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "llvm.func"()  <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
        %a = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %b = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
        %trunc = "gmir.g_trunc"(%a) : (i64) -> i32
        // CHECK:      %[[H:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[H]]) : (!riscv.reg) -> i32
        %anyext = "gmir.g_anyext"(%b) : (i32) -> i64
        // CHECK:      %[[J:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%[[J]]) : (!riscv.reg) -> i64
        "test.test"(%trunc) : (i32) -> ()
        "test.test"(%anyext) : (i64) -> ()
        "llvm.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
