// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"() ({
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

    %icmp_slt0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 2 : i64}> : (i32, i32) -> i1
    %icmp_slt_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "test.test"(%icmp_slt0, %icmp_slt_commuted) : (i1, i1) -> ()

    // CHECK-NEXT: %[[ICMP_SLT0:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_SLT1:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: "test.test"(%[[ICMP_SLT0]], %[[ICMP_SLT1]]) : (i1, i1) -> ()

    %icmp_sgt_inverse = "llvm.icmp"(%arg1, %arg0) <{predicate = 4 : i64}> : (i32, i32) -> i1
    %icmp_sle0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 3 : i64}> : (i32, i32) -> i1
    %icmp_sge_inverse = "llvm.icmp"(%arg1, %arg0) <{predicate = 5 : i64}> : (i32, i32) -> i1
    %icmp_ult0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 6 : i64}> : (i32, i32) -> i1
    %icmp_ugt_inverse = "llvm.icmp"(%arg1, %arg0) <{predicate = 8 : i64}> : (i32, i32) -> i1
    %icmp_ule0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 7 : i64}> : (i32, i32) -> i1
    %icmp_uge_inverse = "llvm.icmp"(%arg1, %arg0) <{predicate = 9 : i64}> : (i32, i32) -> i1
    "test.test"(%icmp_slt0, %icmp_sgt_inverse, %icmp_sle0, %icmp_sge_inverse, %icmp_ult0, %icmp_ugt_inverse, %icmp_ule0, %icmp_uge_inverse) : (i1, i1, i1, i1, i1, i1, i1, i1) -> ()

    // CHECK-NEXT: %[[ICMP_SLE:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 3 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_ULT:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 6 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_ULE:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 7 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: "test.test"(%[[ICMP_SLT0]], %[[ICMP_SLT0]], %[[ICMP_SLE]], %[[ICMP_SLE]], %[[ICMP_ULT]], %[[ICMP_ULT]], %[[ICMP_ULE]], %[[ICMP_ULE]]) : (i1, i1, i1, i1, i1, i1, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()
