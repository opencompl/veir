// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

  ^1():
    "func.func"() ({
      ^1(%0 : i64):
        
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK: "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> i32
        // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i64
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()

}) : () -> ()