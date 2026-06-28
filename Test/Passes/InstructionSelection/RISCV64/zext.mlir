// RUN: veir-opt %s -p=isel-sdag-riscv64,isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i1, i16, i32) -> ()}> ({
    ^bb0(%a: i1, %b: i16, %c: i32, %d: i42):
        %sexta = "llvm.zext"(%b) : (i16) -> i64
        %sextb = "llvm.zext"(%b) : (i16) -> i32
        %sextc = "llvm.zext"(%c) : (i32) -> i64
        %sextd = "llvm.zext"(%a) : (i1) -> i64
        %zextd = "llvm.zext"(%a) : (i8) -> i32
        // CHECK:           ^{{.*}}([[A:.*]] : i1, [[B:.*]] : i16, [[C:.*]] : i32, [[D:.*]] : i42):
        // CHECK-NEXT:      %[[E:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[F:.*]] = "riscv.zexth"(%[[E]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[G:.*]] = "builtin.unrealized_conversion_cast"(%[[F]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i16) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "riscv.zexth"(%[[H]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[J:.*]] = "builtin.unrealized_conversion_cast"(%[[I]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[L:.*]] = "riscv.zextw"(%[[K]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[M:.*]] = "builtin.unrealized_conversion_cast"(%[[L]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i1) -> !riscv.reg
        // CHECK-NEXT:      %[[O:.*]] = "riscv.andi"(%[[N]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[P:.*]] = "builtin.unrealized_conversion_cast"(%[[O]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[A]]) : (i8) -> !riscv.reg
        // CHECK-NEXT:      %[[O:.*]] = "riscv.zextb"(%[[N]]) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:      %[[P:.*]] = "builtin.unrealized_conversion_cast"(%[[O]]) : (!riscv.reg) -> i32
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

