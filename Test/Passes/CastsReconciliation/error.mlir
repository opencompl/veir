// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

  ^1():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i8
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i8) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:         "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i8
        // CHECK-NEXT:    "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> i64
        // CHECK-NEXT:    "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^2():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        %3 = "builtin.unrealized_conversion_cast"(%2) : (i32) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:         "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT:    "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> i32
        // CHECK-NEXT:    "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i64
        // CHECK-NEXT:    "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

}) : () -> ()
