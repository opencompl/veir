// RUN: veir-opt %s -p=dce| filecheck %s



"builtin.module"() ({
  
  // An operation that returns one unused result
  ^4():
    "func.func"() ({
      ^6(%1 : i64):
        %2 = "test.test"(%1) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:      "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
  
  // A chain of operations that is eventually unused
  ^5():
    "func.func"() ({
      ^6():
        %1 = "test.test"() : () -> i64
        %2 = "test.test"(%1) : (i64) -> i64
        %3 = "test.test"(%1, %2) : (i64, i64) -> i64
        %4 = "test.test"(%3) : (i64) -> i64
        %5 = "test.test"(%4, %4) : (i64, i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:      %{{.*}} = "test.test"() : () -> i64
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
  
  // A chain of operations that is eventually used
  ^6():
    "func.func"() ({
      ^6():
        %1 = "test.test"() : () -> i64
        %2 = "test.test"(%1) : (i64) -> i64
        %3 = "test.test"(%1, %2) : (i64, i64) -> i64
        %4 = "test.test"(%3) : (i64) -> i64
        %5 = "test.test"(%4, %4) : (i64, i64) -> i64
        "test.test"(%5) : (i64) -> ()
        // CHECK:      %{{.*}} = "test.test"() : () -> i64
        // CHECK-NEXT: %{{.*}} = "test.test"(%{{.*}}) : (i64) -> i64    
        // CHECK-NEXT: %{{.*}} = "test.test"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64    
        // CHECK-NEXT: %{{.*}} = "test.test"(%{{.*}}) : (i64) -> i64    
        // CHECK-NEXT: %{{.*}} = "test.test"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64    
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
}) : () -> ()

