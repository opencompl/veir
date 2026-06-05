// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i8, i16, i32, i42) -> ()}> ({
    ^bb0(%a: i8, %b: i16, %c: i32, %d: i42):
        %zexta = "llvm.zext"(%a) : (i8) -> i16
        %zextb = "llvm.zext"(%b) : (i16) -> i32
        %zextc = "llvm.zext"(%c) : (i32) -> i64
        %sexdt = "llvm.zext"(%d) : (i42) -> i54
        
        // CHECK:           ^{{.*}}([[A:.*]] : i8, [[B:.*]] : i16, [[C:.*]] : i32, [[D:.*]] : i42):
        // CHECK-NEXT:      %[[E:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i8) -> !riscv.reg
        // CHECK-NEXT:      %[[F:.*]] = "riscv.zextb"(%[[E]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[G:.*]] = "builtin.unrealized_conversion_cast"(%[[F]]) : (!riscv.reg) -> i16
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "riscv.zexth"(%[[H]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[J:.*]] = "builtin.unrealized_conversion_cast"(%[[I]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[L:.*]] = "riscv.zextw"(%[[K]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[M:.*]] = "builtin.unrealized_conversion_cast"(%[[L]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (i42) -> !riscv.reg
        // CHECK-NEXT:      %[[O:.*]] = "riscv.slli"(%[[N]]) <{"value" = 22 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[P:.*]] = "riscv.srli"(%[[O]]) <{"value" = 22 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[Q:.*]] = "builtin.unrealized_conversion_cast"(%[[P]]) : (!riscv.reg) -> i54
        
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

