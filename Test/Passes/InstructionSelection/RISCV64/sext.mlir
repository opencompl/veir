// RUN: veir-opt %s -p=isel-sdag-riscv64,isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i1, i16, i32, i42, i8) -> ()}> ({
    ^bb0(%a: i1, %b: i16, %c: i32, %d: i42, %e: i8):
        %sexta = "llvm.sext"(%b) : (i16) -> i64
        %sextb = "llvm.sext"(%b) : (i16) -> i32
        %sextc = "llvm.sext"(%c) : (i32) -> i64
        %sextd = "llvm.sext"(%a) : (i1) -> i64
        %sexte = "llvm.sext"(%e) : (i8) -> i64
        // CHECK:           ^{{.*}}([[A:.*]] : i1, [[B:.*]] : i16, [[C:.*]] : i32, [[D:.*]] : i42, [[E:.*]] : i8):
        // CHECK-NEXT:      %[[F:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[G:.*]] = "riscv.sexth"(%[[F]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"(%[[G]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[J:.*]] = "riscv.sexth"(%[[I]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"(%[[J]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:      %[[L:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[M:.*]] = "riscv.sextw"(%[[L]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"(%[[M]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[O:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
        // CHECK-NEXT:      %[[P:.*]] = "riscv.slli"(%[[O]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[Q:.*]] = "riscv.srai"(%[[P]]) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[R:.*]] = "builtin.unrealized_conversion_cast"(%[[Q]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[S:.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (i8) -> !riscv.reg
        // CHECK-NEXT:      %[[T:.*]] = "riscv.sextb"(%[[S]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[U:.*]] = "builtin.unrealized_conversion_cast"(%[[T]]) : (!riscv.reg) -> i64
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

