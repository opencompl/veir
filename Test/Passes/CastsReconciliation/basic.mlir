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
        // the remaining cast is unused 
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK: ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT: "test.test"([[ARG]]) : (i64) -> ()
    }) : () -> ()

  ^4():
    "func.func"() ({
      ^1(%0 : i64):
        // the remaining cast is used
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "test.test"(%1) : (i32) -> (i32)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        "test.test"(%2, %3) : (i32, i64) -> ()
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   %{{.*}} = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> i32
        // CHECK-NEXT:   %{{.*}} = "test.test"(%{{.*}}) : (i32) -> i32
        // CHECK-NEXT:   "test.test"(%{{.*}}, [[ARG]]) : (i32, i64) -> ()  
    }) : () -> ()
    
  ^5():
    "func.func"() ({
      ^1(%0 : i64):
        // we only fold pairs of casts, not chains
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i8
        %3 = "builtin.unrealized_conversion_cast"(%2) : (i8) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:        %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
        // CHECK-NEXT:   %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i8
        // CHECK-NEXT:   %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> i64
        // CHECK-NEXT:   "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()

  
  ^6():
    "func.func"() ({
      ^1(%0 : i64):
        // pairs of casts, the remaining ones are unused
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i8
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (i8) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]], [[ARG]]) : (i64, i64) -> ()
    }) : () -> ()
    
  ^8():
    "func.func"() ({
      ^1(%0 : i32):
        // identity cast on block argument
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> i32
        "test.test"(%1) : (i32) -> ()
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i32):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (i32) -> ()
    }) : () -> ()



}) : () -> ()