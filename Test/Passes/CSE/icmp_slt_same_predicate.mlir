// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"() ({
^bb0(%arg0 : i32, %arg1 : i32):
    %icmp_slt0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 2 : i64}> : (i32, i32) -> i1
    %icmp_slt_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "test.test"(%icmp_slt0, %icmp_slt_commuted) : (i1, i1) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[ICMP_SLT0:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_SLT1:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: "test.test"(%[[ICMP_SLT0]], %[[ICMP_SLT1]]) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()
