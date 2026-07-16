// RUN: veir-opt %s -p=dce| filecheck %s



"builtin.module"() ({
  
  // An operation that returns one unused result
    "func.func"()  <{function_type = (i64) -> (), sym_name = "foo"}> ({
      ^6(%1 : i64):
        %2 = "llvm.add"(%1, %1) : (i64, i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // The unused %2 is removed; the sink stays right after the block header.
        // CHECK:      "func.func"() <{"function_type" = (i64) -> (), "sym_name" = "foo"}> ({
        // CHECK-NEXT: ^{{.*}}(%{{.*}} : i64):
        // CHECK-NEXT: "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
  
  // A chain of operations that is eventually unused
    "func.func"()  <{function_type = () -> (), sym_name = "bar"}> ({
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
    "func.func"()  <{function_type = () -> (), sym_name = "baz"}> ({
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

