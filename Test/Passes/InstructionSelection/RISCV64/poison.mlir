// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// `g_poison` is selected as `li 0`, for integers and pointers.

"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
        %one = "gmir.g_poison"() : () -> i1
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i1
        %two = "gmir.g_poison"() : () -> i32
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i32
        %three = "gmir.g_poison"() : () -> i64
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> i64
        %four = "gmir.g_poison"() : () -> !llvm.ptr
        // CHECK: [[A:%.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"([[A]]) : (!riscv.reg) -> !llvm.ptr
        "test.test"(%one) : (i1) -> ()
        "test.test"(%two) : (i32) -> ()
        "test.test"(%three) : (i64) -> ()
        "test.test"(%four) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
