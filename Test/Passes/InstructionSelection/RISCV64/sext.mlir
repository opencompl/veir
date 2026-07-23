// RUN: veir-opt %s -p=isel-sdag-riscv64,isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i1, i16, i32, i42, i8) -> (), sym_name = "foo"}> ({
    ^bb0(%a: i1, %b: i16, %c: i32, %d: i42, %e: i8):
        %sexta = "llvm.sext"(%b) : (i16) -> i64
        %sextb = "llvm.sext"(%b) : (i16) -> i32
        %sextc = "llvm.sext"(%c) : (i32) -> i64
        %sextd = "llvm.sext"(%a) : (i1) -> i64
        %sexte = "llvm.sext"(%a) : (i1) -> i32
        %sextf = "llvm.sext"(%e) : (i8) -> i64
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
        // CHECK-NEXT:      %[[P:.*]] = "riscv.slli"(%[[O]]) <{"value" = 63 : i6}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[Q:.*]] = "riscv.srai"(%[[P]]) <{"value" = 63 : i6}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[R:.*]] = "builtin.unrealized_conversion_cast"(%[[Q]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[S:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
        // CHECK-NEXT:      %[[T:.*]] = "riscv.slli"(%[[S]]) <{"value" = 63 : i6}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[U:.*]] = "riscv.srai"(%[[T]]) <{"value" = 63 : i6}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[V:.*]] = "builtin.unrealized_conversion_cast"(%[[U]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:      %[[W:.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (i8) -> !riscv.reg
        // CHECK-NEXT:      %[[X:.*]] = "riscv.sextb"(%[[W]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[Y:.*]] = "builtin.unrealized_conversion_cast"(%[[X]]) : (!riscv.reg) -> i64
        "test.test"(%sexta) : (i64) -> ()
        "test.test"(%sextb) : (i32) -> ()
        "test.test"(%sextc) : (i64) -> ()
        "test.test"(%sextd) : (i64) -> ()
        "test.test"(%sexte) : (i32) -> ()
        "test.test"(%sextf) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

