// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i8, %b: i16, %c: i32, %d: i42):
        %trunca = "llvm.trunc"(%a) : (i8) -> i4
        %truncb = "llvm.trunc"(%b) : (i16) -> i13
        %truncc = "llvm.trunc"(%c) : (i32) -> i8
        %sexdt = "llvm.trunc"(%d) : (i42) -> i37
        
        // CHECK:           ^{{.*}}([[A:.*]] : i8, [[B:.*]] : i16, [[C:.*]] : i32, [[D:.*]] : i42):
        // CHECK-NEXT:      %[[E:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i8) -> !riscv.reg
        // CHECK-NEXT:      %[[F:.*]] = "builtin.unrealized_conversion_cast"(%[[E]]) : (!riscv.reg) -> i4
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"(%[[H]]) : (!riscv.reg) -> i13
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[L:.*]] = "builtin.unrealized_conversion_cast"(%[[K]]) : (!riscv.reg) -> i8
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (i42) -> !riscv.reg
        // CHECK-NEXT:      %[[Q:.*]] = "builtin.unrealized_conversion_cast"(%[[N]]) : (!riscv.reg) -> i37
        
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

