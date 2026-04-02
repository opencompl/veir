// RUN: veir-opt %s -p=reconcile-cast| filecheck %s

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6(%1 : i64):
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:      "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
    
    ^5():
    "func.func"() ({
      ^6(%1 : i64):
        %2 = "test.test"(%1) : (i64) -> i64
        %3 = "test.test"(%1, %2) : (i64, i64) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (i64) -> i64
        "test.test"(%4) : (i64) -> ()
        // CHECK:      "test.test"(%{{.*}}) : (i64) -> i64
        // CHECK-NEXT: "test.test"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64    
        // CHECK-NEXT:      "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
}) : () -> ()

