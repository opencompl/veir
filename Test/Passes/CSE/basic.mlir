// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"() ({
^bb0(%arg0 : i32, %arg1 : i32):
    %sum0 = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    %sum1 = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    %sum_commuted = "llvm.add"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%sum0, %sum1, %sum_commuted) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[SUM:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SUM]], %[[SUM]], %[[SUM]]) : (i32, i32, i32) -> ()

    %sub0 = "llvm.sub"(%arg0, %arg1) : (i32, i32) -> i32
    %sub1 = "llvm.sub"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%sub0, %sub1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[SUB0:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[SUB1:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SUB0]], %[[SUB1]]) : (i32, i32) -> ()

    "llvm.return"() : () -> ()
^bb1(%arg2 : i32, %arg3 : i32):
    %sum_other_block = "llvm.add"(%arg2, %arg3) : (i32, i32) -> i32
    "test.test"(%sum_other_block) : (i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[OTHER:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[OTHER]]) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
