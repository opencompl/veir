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

    %and0 = "llvm.and"(%arg0, %arg1) : (i32, i32) -> i32
    %and1 = "llvm.and"(%arg1, %arg0) : (i32, i32) -> i32
    %xor0 = "llvm.xor"(%arg0, %arg1) : (i32, i32) -> i32
    %xor1 = "llvm.xor"(%arg1, %arg0) : (i32, i32) -> i32
    "test.test"(%and0, %and1, %xor0, %xor1) : (i32, i32, i32, i32) -> ()

    // CHECK-NEXT: %[[AND:.*]] = "llvm.and"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: %[[XOR:.*]] = "llvm.xor"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[AND]], %[[AND]], %[[XOR]], %[[XOR]]) : (i32, i32, i32, i32) -> ()

    %cond0 = "test.source"() : () -> i1
    %cond1 = "test.source"() : () -> i1
    %select0 = "llvm.select"(%cond0, %arg0, %arg1) : (i1, i32, i32) -> i32
    %select1 = "llvm.select"(%cond0, %arg0, %arg1) : (i1, i32, i32) -> i32
    %select_swapped = "llvm.select"(%cond1, %arg1, %arg0) : (i1, i32, i32) -> i32
    "test.test"(%select0, %select1, %select_swapped) : (i32, i32, i32) -> ()

    // CHECK-NEXT: %[[COND0:.*]] = "test.source"() : () -> i1
    // CHECK-NEXT: %[[COND1:.*]] = "test.source"() : () -> i1
    // CHECK-NEXT: %[[SELECT:.*]] = "llvm.select"(%[[COND0]], %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: %[[SELECT_SWAPPED:.*]] = "llvm.select"(%[[COND1]], %{{.*}}, %{{.*}}) : (i1, i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SELECT]], %[[SELECT]], %[[SELECT_SWAPPED]]) : (i32, i32, i32) -> ()

    %sext0 = "llvm.sext"(%cond0) : (i1) -> i32
    %sext1 = "llvm.sext"(%cond0) : (i1) -> i32
    %zext_i16 = "llvm.zext"(%cond0) : (i1) -> i16
    %zext_i32 = "llvm.zext"(%cond0) : (i1) -> i32
    %zext_i32_dup = "llvm.zext"(%cond0) : (i1) -> i32
    "test.test"(%sext0, %sext1, %zext_i16, %zext_i32, %zext_i32_dup) : (i32, i32, i16, i32, i32) -> ()

    // CHECK-NEXT: %[[SEXT:.*]] = "llvm.sext"(%[[COND0]]) : (i1) -> i32
    // CHECK-NEXT: %[[ZEXT_I16:.*]] = "llvm.zext"(%[[COND0]]) : (i1) -> i16
    // CHECK-NEXT: %[[ZEXT_I32:.*]] = "llvm.zext"(%[[COND0]]) : (i1) -> i32
    // CHECK-NEXT: "test.test"(%[[SEXT]], %[[SEXT]], %[[ZEXT_I16]], %[[ZEXT_I32]], %[[ZEXT_I32]]) : (i32, i32, i16, i32, i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
