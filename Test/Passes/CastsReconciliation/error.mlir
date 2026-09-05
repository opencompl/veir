// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

    "func.func"()  <{function_type = (i64) -> (), sym_name = "foo"}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i8
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i8) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:         func.func @foo([[ARG:%.*]]: i64) {
        // CHECK-NEXT:    [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> i8
        // CHECK-NEXT:    [[C2:%.*]] = "builtin.unrealized_conversion_cast"([[C1]]) : (i8) -> i64
        // CHECK-NEXT:    "test.test"([[C2]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    "func.func"()  <{function_type = (i64) -> (), sym_name = "bar"}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        %3 = "builtin.unrealized_conversion_cast"(%2) : (i32) -> i64
        "test.test"(%3) : (i64) -> ()
        // No pair of adjacent casts returns to its own input type, so the chain stays.
        // CHECK:         func.func @bar([[ARG:%.*]]: i64) {
        // CHECK-NEXT:    [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> !riscv.reg
        // CHECK-NEXT:    [[C2:%.*]] = "builtin.unrealized_conversion_cast"([[C1]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:    [[C3:%.*]] = "builtin.unrealized_conversion_cast"([[C2]]) : (i32) -> i64
        // CHECK-NEXT:    "test.test"([[C3]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
