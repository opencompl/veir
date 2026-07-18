// RUN: veir-opt %s -p=cse | filecheck %s

// Tests that the CSE pass treats nsw/nuw flags as part of an operation's
// identity: ops with the same flags merge, ops with differing flag sets do not,
// and flags are never silently dropped.

"builtin.module"() ({
  "llvm.func"()  <{function_type = !llvm.func<void (i32, i32)>, sym_name = "foo"}> ({

// `add nsw` merges with `add nsw`; flagless `add` stays separate.
^add_nsw(%a : i32, %b : i32):
    %add_nsw_1 = "llvm.add"(%a, %b) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %add_nsw_2 = "llvm.add"(%a, %b) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %add_plain = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%add_nsw_1, %add_nsw_2, %add_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[ADD_NSW:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_PLAIN:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_NSW]], %[[ADD_NSW]], %[[ADD_PLAIN]])

// `add nsw`, `add nuw`, and `add nsw,nuw` all remain distinct; the duplicate
// `add nsw,nuw` does merge with itself.
    "llvm.return"() : () -> ()
^add_flags(%c : i32, %d : i32):
    %add_nsw_only = "llvm.add"(%c, %d) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %add_nuw_only = "llvm.add"(%c, %d) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %add_both_a   = "llvm.add"(%c, %d) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
    %add_both_b   = "llvm.add"(%c, %d) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
    "test.test"(%add_nsw_only, %add_nuw_only, %add_both_a, %add_both_b) : (i32, i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[ADD_NSW_ONLY:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_NUW_ONLY:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_BOTH:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_NSW_ONLY]], %[[ADD_NUW_ONLY]], %[[ADD_BOTH]], %[[ADD_BOTH]])

// Commutativity applies under matching flags: `add nsw a b` and `add nsw b a` merge.
    "llvm.return"() : () -> ()
^add_comm(%e : i32, %f : i32):
    %add_comm_1 = "llvm.add"(%e, %f) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %add_comm_2 = "llvm.add"(%f, %e) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    "test.test"(%add_comm_1, %add_comm_2) : (i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[ADD_COMM:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_COMM]], %[[ADD_COMM]])

// `mul nsw` vs `mul nuw` are distinct; `mul nsw` with commuted operands merges.
    "llvm.return"() : () -> ()
^mul_flags(%g : i32, %h : i32):
    %mul_nsw = "llvm.mul"(%g, %h) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %mul_nuw = "llvm.mul"(%g, %h) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %mul_nsw_dup = "llvm.mul"(%h, %g) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    "test.test"(%mul_nsw, %mul_nuw, %mul_nsw_dup) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[MUL_NSW:.*]] = "llvm.mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[MUL_NUW:.*]] = "llvm.mul"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[MUL_NSW]], %[[MUL_NUW]], %[[MUL_NSW]])

// `sub` is non-commutative; nsw still partitions identity.
    "llvm.return"() : () -> ()
^sub_flags(%i : i32, %j : i32):
    %sub_nsw_1 = "llvm.sub"(%i, %j) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %sub_nsw_2 = "llvm.sub"(%i, %j) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %sub_plain = "llvm.sub"(%i, %j) : (i32, i32) -> i32
    "test.test"(%sub_nsw_1, %sub_nsw_2, %sub_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[SUB_NSW:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SUB_PLAIN:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SUB_NSW]], %[[SUB_NSW]], %[[SUB_PLAIN]])

// `shl` carries nsw/nuw; three flag combos must remain three ops.
    "llvm.return"() : () -> ()
^shl_flags(%k : i32, %l : i32):
    %shl_nsw_1 = "llvm.shl"(%k, %l) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %shl_nsw_2 = "llvm.shl"(%k, %l) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %shl_nuw   = "llvm.shl"(%k, %l) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %shl_plain = "llvm.shl"(%k, %l) : (i32, i32) -> i32
    "test.test"(%shl_nsw_1, %shl_nsw_2, %shl_nuw, %shl_plain) : (i32, i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[SHL_NSW:.*]] = "llvm.shl"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SHL_NUW:.*]] = "llvm.shl"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SHL_PLAIN:.*]] = "llvm.shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SHL_NSW]], %[[SHL_NSW]], %[[SHL_NUW]], %[[SHL_PLAIN]])

// `trunc` carries nsw/nuw; three flag combos remain three ops.
    "llvm.return"() : () -> ()
^trunc_flags(%t : i64):
    %trunc_nsw  = "llvm.trunc"(%t) <{"overflowFlags" = 1 : i32}> : (i64) -> i32
    %trunc_nuw  = "llvm.trunc"(%t) <{"overflowFlags" = 2 : i32}> : (i64) -> i32
    %trunc_both_1 = "llvm.trunc"(%t) <{"overflowFlags" = 3 : i32}> : (i64) -> i32
    %trunc_both_2 = "llvm.trunc"(%t) <{"overflowFlags" = 3 : i32}> : (i64) -> i32
    "test.test"(%trunc_nsw, %trunc_nuw, %trunc_both_1, %trunc_both_2) : (i32, i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i64):
    // CHECK-NEXT: %[[TRUNC_NSW:.*]] = "llvm.trunc"(%{{.*}}) <{"overflowFlags" = 1 : i32}> : (i64) -> i32
    // CHECK-NEXT: %[[TRUNC_NUW:.*]] = "llvm.trunc"(%{{.*}}) <{"overflowFlags" = 2 : i32}> : (i64) -> i32
    // CHECK-NEXT: %[[TRUNC_BOTH:.*]] = "llvm.trunc"(%{{.*}}) <{"overflowFlags" = 3 : i32}> : (i64) -> i32
    // CHECK-NEXT: "test.test"(%[[TRUNC_NSW]], %[[TRUNC_NUW]], %[[TRUNC_BOTH]], %[[TRUNC_BOTH]])
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
