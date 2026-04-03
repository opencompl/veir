// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

  ^1():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i256
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i256) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:         "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i256
        // CHECK-NEXT:    "builtin.unrealized_conversion_cast"(%{{.*}}) : (i256) -> i64
        // CHECK-NEXT:    "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()

  ^2():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!reg) -> i256
        %3 = "builtin.unrealized_conversion_cast"(%2) : (i256) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:         "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT:    "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i256
        // CHECK-NEXT:    "builtin.unrealized_conversion_cast"(%{{.*}}) : (i256) -> i64
        // CHECK-NEXT:    "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()

}) : () -> ()