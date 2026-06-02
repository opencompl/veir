// RUN: veir-opt %s -p=dce| filecheck %s



"builtin.module"() ({
  
  // An operation that returns one unused result
  ^4():
    "func.func"() ({
      ^6(%1 : i64):
        %2 = "llvm.add"(%1, %1) : (i64, i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // The unused %2 is removed; the sink stays right after the block header.
        // CHECK:      "func.func"() ({
        // CHECK-NEXT: ^{{.*}}(%{{.*}} : i64):
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
  
  // A chain of operations that is eventually unused
  ^5():
    "func.func"() ({
      ^6():
        %1 = "arith.constant"() <{ "value" = 1 : i64 }> : () -> i64
        %2 = "llvm.add"(%1, %1) : (i64, i64) -> i64
        %3 = "llvm.add"(%1, %2) : (i64, i64) -> i64
        %4 = "llvm.add"(%3, %3) : (i64, i64) -> i64
        %5 = "llvm.add"(%4, %4) : (i64, i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // The dead chain %2..%5 is removed; %1 stays because the sink uses it.
        // CHECK:      %{{.*}} = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
  
  // A chain of operations that is eventually used
  ^6():
    "func.func"() ({
      ^6():
        %1 = "arith.constant"() <{ "value" = 1 : i64 }> : () -> i64
        %2 = "llvm.add"(%1, %1) : (i64, i64) -> i64
        %3 = "llvm.add"(%1, %2) : (i64, i64) -> i64
        %4 = "llvm.add"(%3, %3) : (i64, i64) -> i64
        %5 = "llvm.add"(%4, %4) : (i64, i64) -> i64
        "test.test"(%5) : (i64) -> ()
        // The whole chain is live because the sink uses %5.
        // CHECK:      %{{.*}} = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        // CHECK-NEXT: %{{.*}} = "llvm.add"(%{{.*}}, %{{.*}}) : (i64, i64) -> i64
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

