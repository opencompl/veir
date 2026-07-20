// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

// Note: `reconcile-cast` unconditionally coerces `i64` function arguments to
// `!riscv.reg`, inserting a boundary `reg -> i64` cast (see `basic.mlir` and
// `coerce_function_boundaries.mlir`). Below that boundary cast reconciles into the
// body's own leading cast where legal, leaving the truncating round trips these cases
// exist to test untouched.

"builtin.module"() ({

  ^1():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "foo"}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i8
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i8) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:         ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:    [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i64
        // CHECK-NEXT:    [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[C0]]) : (i64) -> i8
        // CHECK-NEXT:    [[C2:%.*]] = "builtin.unrealized_conversion_cast"([[C1]]) : (i8) -> i64
        // CHECK-NEXT:    "test.test"([[C2]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^2():
    "func.func"()  <{function_type = (i64) -> (), sym_name = "bar"}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        %3 = "builtin.unrealized_conversion_cast"(%2) : (i32) -> i64
        "test.test"(%3) : (i64) -> ()
        // The boundary's `reg -> i64` cast pairs with the body's `i64 -> reg` cast
        // (legal both ways for `i64`) and both reconcile away, leaving the `reg -> i32
        // -> i64` chain, which isn't a round trip back to `reg` so it stays.
        // CHECK:         ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:    [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:    [[C2:%.*]] = "builtin.unrealized_conversion_cast"([[C1]]) : (i32) -> i64
        // CHECK-NEXT:    "test.test"([[C2]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
