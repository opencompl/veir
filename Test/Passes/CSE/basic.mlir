// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
^bb0(%arg0 : i32, %arg1 : i32, %ptr : !llvm.ptr):
    %sum0 = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    %sum1 = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    %sum_commuted = "llvm.add"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%sum0, %sum1, %sum_commuted) : (i32, i32, i32) -> ()

    // CHECK:      %[[SUM:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SUM]], %[[SUM]], %[[SUM]]) : (i32, i32, i32) -> ()

    %sub0 = "llvm.sub"(%arg0, %arg1) : (i32, i32) -> i32
    %sub1 = "llvm.sub"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%sub0, %sub1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[SUB0:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[SUB1:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SUB0]], %[[SUB1]]) : (i32, i32) -> ()

    // Pure integer divs and remainders are non-commutative; duplicates with
    // the same operands merge, swapped operands stay distinct. Soundness
    // under divide-by-zero / signed-overflow UB: the surviving op is always
    // above the erased one in the same block, so any UB triggered by the
    // duplicate is already triggered by the survivor.
    %udiv0 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32
    %udiv1 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32
    %udiv_swap = "llvm.udiv"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%udiv0, %udiv1, %udiv_swap) : (i32, i32, i32) -> ()

    // CHECK:      %[[UDIV:.*]] = "llvm.udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[UDIV_SWAP:.*]] = "llvm.udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[UDIV]], %[[UDIV]], %[[UDIV_SWAP]]) : (i32, i32, i32) -> ()

    %sdiv0 = "llvm.sdiv"(%arg0, %arg1) : (i32, i32) -> i32
    %sdiv1 = "llvm.sdiv"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%sdiv0, %sdiv1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[SDIV:.*]] = "llvm.sdiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SDIV]], %[[SDIV]]) : (i32, i32) -> ()

    %urem0 = "llvm.urem"(%arg0, %arg1) : (i32, i32) -> i32
    %urem1 = "llvm.urem"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%urem0, %urem1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[UREM:.*]] = "llvm.urem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[UREM]], %[[UREM]]) : (i32, i32) -> ()

    %srem0 = "llvm.srem"(%arg0, %arg1) : (i32, i32) -> i32
    %srem1 = "llvm.srem"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%srem0, %srem1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[SREM:.*]] = "llvm.srem"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SREM]], %[[SREM]]) : (i32, i32) -> ()

    %load0 = "llvm.load"(%ptr) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
    %load1 = "llvm.load"(%ptr) <{"access_groups" = [], "alias_scopes" = [], "alignment" = 4 : i64, "noalias_scopes" = [], "tbaa" = []}> : (!llvm.ptr) -> i32
    "test.test"(%load0, %load1) : (i32, i32) -> ()

    // CHECK-NEXT: %[[LOAD0:.*]] = "llvm.load"(%{{.*}}) <{{.*}}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: %[[LOAD1:.*]] = "llvm.load"(%{{.*}}) <{{.*}}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: "test.test"(%[[LOAD0]], %[[LOAD1]]) : (i32, i32) -> ()

^bb1(%arg2 : i32, %arg3 : i32):
    %sum_other_block = "llvm.add"(%arg2, %arg3) : (i32, i32) -> i32
    "test.test"(%sum_other_block) : (i32) -> ()

    // CHECK:      %[[OTHER:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[OTHER]]) : (i32) -> ()
}) : () -> ()
