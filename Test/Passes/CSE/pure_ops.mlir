// RUN: veir-opt %s -p=cse | filecheck %s

"builtin.module"() ({
  "llvm.func"() ({
^bb0(%arg0 : i32, %arg1 : i32):
    // Pure integer divs and remainders are non-commutative; duplicates with
    // the same operands merge, swapped operands stay distinct. Soundness
    // under divide-by-zero / signed-overflow UB: the surviving op is always
    // above the erased one in the same block, so any UB triggered by the
    // duplicate is already triggered by the survivor.
    %udiv0 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32
    %udiv1 = "llvm.udiv"(%arg0, %arg1) : (i32, i32) -> i32
    %udiv_swap = "llvm.udiv"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%udiv0, %udiv1, %udiv_swap) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
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

    %icmp_eq0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %icmp_eq_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %icmp_ne0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 1 : i64}> : (i32, i32) -> i1
    %icmp_ne_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 1 : i64}> : (i32, i32) -> i1
    "test.test"(%icmp_eq0, %icmp_eq_commuted, %icmp_ne0, %icmp_ne_commuted) : (i1, i1, i1, i1) -> ()

    // CHECK-NEXT: %[[ICMP_EQ:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_NE:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: "test.test"(%[[ICMP_EQ]], %[[ICMP_EQ]], %[[ICMP_NE]], %[[ICMP_NE]]) : (i1, i1, i1, i1) -> ()

    %icmp_slt0 = "llvm.icmp"(%arg0, %arg1) <{predicate = 2 : i64}> : (i32, i32) -> i1
    %icmp_slt_commuted = "llvm.icmp"(%arg1, %arg0) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "test.test"(%icmp_slt0, %icmp_slt_commuted) : (i1, i1) -> ()

    // CHECK-NEXT: %[[ICMP_SLT0:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: %[[ICMP_SLT1:.*]] = "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NEXT: "test.test"(%[[ICMP_SLT0]], %[[ICMP_SLT1]]) : (i1, i1) -> ()

    %and0 = "llvm.and"(%arg0, %arg1) : (i32, i32) -> i32
    %and1 = "llvm.and"(%arg1, %arg0) : (i32, i32) -> i32
    %xor0 = "llvm.xor"(%arg0, %arg1) : (i32, i32) -> i32
    %xor1 = "llvm.xor"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%and0, %and1, %xor0, %xor1) : (i32, i32, i32, i32) -> ()

    // CHECK-NEXT: %[[AND:.*]] = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[XOR:.*]] = "llvm.xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[AND]], %[[AND]], %[[XOR]], %[[XOR]]) : (i32, i32, i32, i32) -> ()

    %cond = "llvm.icmp"(%arg0, %arg1) <{predicate = 0 : i64}> : (i32, i32) -> i1
    %select0 = "llvm.select"(%cond, %arg0, %arg1) : (i1, i32, i32) -> i32
    %select1 = "llvm.select"(%cond, %arg0, %arg1) : (i1, i32, i32) -> i32
    %select_swapped = "llvm.select"(%cond, %arg1, %arg0) : (i1, i32, i32) -> i32
    "test.test"(%select0, %select1, %select_swapped) : (i32, i32, i32) -> ()

    // CHECK-NEXT: %[[SELECT:.*]] = "llvm.select"(%[[ICMP_EQ]], %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[SELECT_SWAPPED:.*]] = "llvm.select"(%[[ICMP_EQ]], %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SELECT]], %[[SELECT]], %[[SELECT_SWAPPED]]) : (i32, i32, i32) -> ()

    %sext0 = "llvm.sext"(%cond) : (i1) -> i32
    %sext1 = "llvm.sext"(%cond) : (i1) -> i32
    %zext_i16 = "llvm.zext"(%cond) : (i1) -> i16
    %zext_i32 = "llvm.zext"(%cond) : (i1) -> i32
    %zext_i32_dup = "llvm.zext"(%cond) : (i1) -> i32
    "test.test"(%sext0, %sext1, %zext_i16, %zext_i32, %zext_i32_dup) : (i32, i32, i16, i32, i32) -> ()

    // CHECK-NEXT: %[[SEXT:.*]] = "llvm.sext"(%[[ICMP_EQ]]) : (i1) -> i32
    // CHECK-NEXT: %[[ZEXT_I16:.*]] = "llvm.zext"(%[[ICMP_EQ]]) : (i1) -> i16
    // CHECK-NEXT: %[[ZEXT_I32:.*]] = "llvm.zext"(%[[ICMP_EQ]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[SEXT]], %[[SEXT]], %[[ZEXT_I16]], %[[ZEXT_I32]], %[[ZEXT_I32]]) : (i32, i32, i16, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()
