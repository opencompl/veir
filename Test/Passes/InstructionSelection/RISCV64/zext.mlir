// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"() ({
    ^bb0(%a: i8, %b: i16, %c: i32, %d: i42):
        %zexta = "llvm.zext"(%a) : (i8) -> i16
        %zextb = "llvm.zext"(%b) : (i16) -> i32
        %zextc = "llvm.zext"(%c) : (i32) -> i64
        %sexdt = "llvm.zext"(%d) : (i42) -> i54
        
        // CHECK:           ^{{.*}}([[A:.*]] : i8, [[B:.*]] : i16, [[C:.*]] : i32, [[D:.*]] : i42):
        // CHECK-NEXT:      %[[E:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i8) -> !reg
        // CHECK-NEXT:      %[[F:.*]] = "riscv.zextb"(%[[E]]) : (!reg) -> !reg
        // CHECK-NEXT:      %[[G:.*]] = "builtin.unrealized_conversion_cast"(%[[F]]) : (!reg) -> i16
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !reg
        // CHECK-NEXT:      %[[I:.*]] = "riscv.zexth"(%[[H]]) : (!reg) -> !reg
        // CHECK-NEXT:      %[[J:.*]] = "builtin.unrealized_conversion_cast"(%[[I]]) : (!reg) -> i32
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !reg
        // CHECK-NEXT:      %[[L:.*]] = "riscv.zextw"(%[[K]]) : (!reg) -> !reg
        // CHECK-NEXT:      %[[M:.*]] = "builtin.unrealized_conversion_cast"(%[[L]]) : (!reg) -> i64
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (i42) -> !reg
        // CHECK-NEXT:      %[[O:.*]] = "riscv.slli"(%[[N]]) <{"value" = 22 : i64}> : (!reg) -> !reg
        // CHECK-NEXT:      %[[P:.*]] = "riscv.srli"(%[[O]]) <{"value" = 22 : i64}> : (!reg) -> !reg
        // CHECK-NEXT:      %[[Q:.*]] = "builtin.unrealized_conversion_cast"(%[[P]]) : (!reg) -> i54
        
    }) : () -> ()
}) : () -> ()

