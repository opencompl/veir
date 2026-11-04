// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{function_type = (i64, i32, i1, i7, i65) -> (), sym_name = "foo"}> ({
    ^bb0(%a : i64, %b: i32, %c: i1, %d: i7, %e: i65):
        %freeze = "llvm.freeze"(%a) : (i64) -> i64
        %freezeinv = "llvm.freeze"(%b) : (i32) -> i32
        %freeze1 = "llvm.freeze"(%c) : (i1) -> i1
        %freeze7 = "llvm.freeze"(%d) : (i7) -> i7
        %freeze65 = "llvm.freeze"(%e) : (i65) -> i65
        // CHECK:           func.func @foo([[B:.*]]: i64, [[C:.*]]: i32, [[D:.*]]: i1, [[E:.*]]: i7, [[F:.*]]: i65) {
        // CHECK-NEXT:      %[[H:.*]] = "builtin.unrealized_conversion_cast"([[B]]) : (i64) -> !riscv.reg
        // CHECK-NEXT:      %[[I:.*]] = "builtin.unrealized_conversion_cast"(%[[H]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:      %[[J:.*]] = "builtin.unrealized_conversion_cast"([[C]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:      %[[K:.*]] = "builtin.unrealized_conversion_cast"(%[[J]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:      %[[L:.*]] = "builtin.unrealized_conversion_cast"([[D]]) : (i1) -> !riscv.reg
        // CHECK-NEXT:      %[[M:.*]] = "builtin.unrealized_conversion_cast"(%[[L]]) : (!riscv.reg) -> i1
        // CHECK-NEXT:      %[[N:.*]] = "builtin.unrealized_conversion_cast"([[E]]) : (i7) -> !riscv.reg
        // CHECK-NEXT:      %[[O:.*]] = "builtin.unrealized_conversion_cast"(%[[N]]) : (!riscv.reg) -> i7
        // CHECK-NEXT:      %[[P:.*]] = "llvm.freeze"([[F]]) : (i65) -> i65

        "test.test"(%freeze) : (i64) -> ()
        "test.test"(%freezeinv) : (i32) -> ()
        "test.test"(%freeze1) : (i1) -> ()
        "test.test"(%freeze7) : (i7) -> ()
        "test.test"(%freeze65) : (i65) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

