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
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2) : (i64) -> ()
        // the remaining cast is unused and caught by DCE, if enabled
        // CHECK: ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:  %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
        // CHECK-NEXT: "test.test"([[ARG]]) : (i64) -> ()
    }) : () -> ()
    
  ^4():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %3 = "test.test"(%1) : (i32) -> (i32)
        %4 = "test.test"(%3) : (i32) -> (i32)
        %5 = "test.test"(%4) : (i32) -> (i32)
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2) : (i64) -> ()
        // the remaining cast is unused and caught by DCE, if enabled
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT   %{{.*}} = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> i32
        // CHECK-NEXT   %{{.*}} = "test.test"(%{{.*}}) : (i32) -> i32
        // CHECK-NEXT   %{{.*}} = "test.test"(%{{.*}}) : (i32) -> i32
        // CHECK-NEXT   %{{.*}} = "test.test"(%{{.*}}) : (i32) -> i32
        // CHECK-NEXT   "test.test"([[ARG]]) : (i64) -> ()
                
    }) : () -> ()


  ^5():
    "func.func"() ({
      ^1(%0 : i64):
        // the remaining cast is used
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "test.test"(%1) : (i32) -> (i32)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2, %3) : (i32, i64) -> ()
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT   %{{.*}} = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> i32
        // CHECK-NEXT   %{{.*}} = "test.test"(%{{.*}}) : (i32) -> i32
        // CHECK-NEXT   "test.test"(%{{.*}}, [[ARG]]) : (i32, i64) -> ()  
    }) : () -> ()
    
}) : () -> ()