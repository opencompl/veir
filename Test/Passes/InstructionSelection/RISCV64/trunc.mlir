// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i16, i32) -> ()}> ({
    ^bb0(%b : i16, %c: i32):
        %truncb = "llvm.trunc"(%b) : (i16) -> i8
        %truncc = "llvm.trunc"(%c) : (i32) -> i16
        
        // CHECK:           ^{{.*}}([[B:.*]] : i16, [[C:.*]] : i32):
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"(%[[H]]) : (!riscv.reg) -> i8
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[L:.*]] = "builtin.unrealized_conversion_cast"(%[[K]]) : (!riscv.reg) -> i16
        
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

