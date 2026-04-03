// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

  ^1():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:      "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
    
  ^2():
    "func.func"() ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        "test.test"(%1) : (!reg) -> ()
        // CHECK:       "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !reg
        // CHECK-NEXT:  "test.test"(%{{.*}}) : (!reg) -> ()
    }) : () -> ()
    
  ^3():
    "func.func"() ({
      ^1(%0 : i64):
        // the remaining cast is unused 
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!reg) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:  "test.test"([[ARG]]) : (i64) -> ()
    }) : () -> ()

  ^4():
    "func.func"() ({
      ^1(%0 : i64):
        // the remaining cast is used
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        %2 = "test.test"(%1) : (!reg) -> (!reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!reg) -> i64
        "test.test"(%2, %3) : (!reg, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   %{{.*}} = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> !reg
        // CHECK-NEXT:   %{{.*}} = "test.test"(%{{.*}}) : (!reg) -> !reg
        // CHECK-NEXT:   "test.test"(%{{.*}}, [[ARG]]) : (!reg, i64) -> ()  
    }) : () -> ()
    
  ^5():
    "func.func"() ({
      ^1(%0 : i64):
        // identity cast and pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!reg) -> !reg
        %3 = "builtin.unrealized_conversion_cast"(%2) : (!reg) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (i64) -> ()
    }) : () -> ()
  
  ^6():
    "func.func"() ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!reg) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (!reg) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]], [[ARG]]) : (i64, i64) -> ()
    }) : () -> ()
    
  ^7():
    "func.func"() ({
      ^1(%0 : !reg):
        // identity cast on block argument
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!reg) -> !reg
        "test.test"(%1) : (!reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !reg):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!reg) -> ()
    }) : () -> ()
  
  ^8():
    "func.func"() ({
      ^1(%0 : i8):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i8) -> i8
        "test.test"(%1) : (i8) -> ()
        // CHECK:        "test.test"(%{{.*}}) : (i8) -> ()
    }) : () -> ()
    
  ^9():
    "func.func"() ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i256
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i128
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i256) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (i128) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]], [[ARG]]) : (i64, i64) -> ()
    }) : () -> ()
    
    

}) : () -> ()
