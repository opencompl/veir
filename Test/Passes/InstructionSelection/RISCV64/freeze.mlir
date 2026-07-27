// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i32) -> (), sym_name = "foo"}> ({
    ^bb0(%a : i64, %b: i32):
        %freeze = "llvm.freeze"(%a) : (i64) -> i64
        %freezeinv = "llvm.freeze"(%b) : (i32) -> i32
        // CHECK:           ^{{.*}}([[B:.*]] : i64, [[C:.*]] : i32):
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"(%[[H]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[J:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"(%[[J]]) : (!riscv.reg) -> i32
        
        "test.test"(%freeze) : (i64) -> ()
        "test.test"(%freezeinv) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

