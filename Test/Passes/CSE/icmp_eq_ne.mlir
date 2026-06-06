// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"()  <{function_type = !llvm.func<void (i32, i32)>}> ({
^bb0(%arg0 : i32, %arg1 : i32):
    %icmp_eq0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %icmp_eq_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %icmp_ne0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    %icmp_ne_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "test.test"(%icmp_eq0, %icmp_eq_commuted, %icmp_ne0, %icmp_ne_commuted) : (i1, i1, i1, i1) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[ICMP_EQ:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_NE:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: "test.test"(%[[ICMP_EQ]], %[[ICMP_EQ]], %[[ICMP_NE]], %[[ICMP_NE]]) : (i1, i1, i1, i1) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
