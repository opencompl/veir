// RUN: veir-opt %s -p=reconcile-cast| filecheck %s

"builtin.module"() ({
  ^4():

    ^5():
    "func.func"() ({
      ^6(%1 : i64):
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i64) -> i32
        %3 = "builtin.unrealized_conversion_cast"(%2) : (i32) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"( %{{.*}}) : (i64) -> i32
        // CHECK-NEXT:      "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
}) : () -> ()

