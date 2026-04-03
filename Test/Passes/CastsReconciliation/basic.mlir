// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

  ^1():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()

  ^2():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        "test.test"(%1) : (i32) -> ()
      // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
      // CHECK-NEXT: "test.test"(%{{.*}}) : (i32) -> ()
    }) : () -> ()
    
  ^3():
    "func.func"() ({
      ^bb1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2) : (i64) -> ()
      // the remaining cast is unused and caught by DCE, if enabled
      // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
      // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
    
}) : () -> ()