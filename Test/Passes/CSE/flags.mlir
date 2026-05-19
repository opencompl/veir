// RUN: veir-opt %s -p=cse | filecheck %s

// Tests that the CSE pass treats UB flags (nsw/nuw/exact/disjoint/nneg) as
// part of an operation's identity: ops with the same flags merge, ops with
// differing flag sets do not, and flags are never silently dropped.
//
// Each scenario lives in its own basic block so the per-block availability
// table cannot bleed between them.

"builtin.module"() ({

// `add nsw` merges with `add nsw`; flagless `add` stays separate.
^add_nsw(%a : i32, %b : i32):
    %add_nsw_1 = "llvm.add"(%a, %b) <{nsw}> : (i32, i32) -> i32
    %add_nsw_2 = "llvm.add"(%a, %b) <{nsw}> : (i32, i32) -> i32
    %add_plain = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%add_nsw_1, %add_nsw_2, %add_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[ADD_NSW:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_PLAIN:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_NSW]], %[[ADD_NSW]], %[[ADD_PLAIN]])

// `add nsw`, `add nuw`, and `add nsw,nuw` all remain distinct; the duplicate
// `add nsw,nuw` does merge with itself.
^add_flags(%c : i32, %d : i32):
    %add_nsw_only = "llvm.add"(%c, %d) <{nsw}> : (i32, i32) -> i32
    %add_nuw_only = "llvm.add"(%c, %d) <{nuw}> : (i32, i32) -> i32
    %add_both_a   = "llvm.add"(%c, %d) <{nuw, nsw}> : (i32, i32) -> i32
    %add_both_b   = "llvm.add"(%c, %d) <{nuw, nsw}> : (i32, i32) -> i32
    "test.test"(%add_nsw_only, %add_nuw_only, %add_both_a, %add_both_b) : (i32, i32, i32, i32) -> ()

    // CHECK:      %[[ADD_NSW_ONLY:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_NUW_ONLY:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ADD_BOTH:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw, nuw}> : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_NSW_ONLY]], %[[ADD_NUW_ONLY]], %[[ADD_BOTH]], %[[ADD_BOTH]])

// Commutativity applies under matching flags: `add nsw a b` and `add nsw b a` merge.
^add_comm(%e : i32, %f : i32):
    %add_comm_1 = "llvm.add"(%e, %f) <{nsw}> : (i32, i32) -> i32
    %add_comm_2 = "llvm.add"(%f, %e) <{nsw}> : (i32, i32) -> i32
    "test.test"(%add_comm_1, %add_comm_2) : (i32, i32) -> ()

    // CHECK:      %[[ADD_COMM:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ADD_COMM]], %[[ADD_COMM]])

// `mul nsw` vs `mul nuw` are distinct; `mul nsw` with commuted operands merges.
^mul_flags(%g : i32, %h : i32):
    %mul_nsw = "llvm.mul"(%g, %h) <{nsw}> : (i32, i32) -> i32
    %mul_nuw = "llvm.mul"(%g, %h) <{nuw}> : (i32, i32) -> i32
    %mul_nsw_dup = "llvm.mul"(%h, %g) <{nsw}> : (i32, i32) -> i32
    "test.test"(%mul_nsw, %mul_nuw, %mul_nsw_dup) : (i32, i32, i32) -> ()

    // CHECK:      %[[MUL_NSW:.*]] = "llvm.mul"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[MUL_NUW:.*]] = "llvm.mul"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[MUL_NSW]], %[[MUL_NUW]], %[[MUL_NSW]])

// `sub` is non-commutative; nsw still partitions identity.
^sub_flags(%i : i32, %j : i32):
    %sub_nsw_1 = "llvm.sub"(%i, %j) <{nsw}> : (i32, i32) -> i32
    %sub_nsw_2 = "llvm.sub"(%i, %j) <{nsw}> : (i32, i32) -> i32
    %sub_plain = "llvm.sub"(%i, %j) : (i32, i32) -> i32
    "test.test"(%sub_nsw_1, %sub_nsw_2, %sub_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[SUB_NSW:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SUB_PLAIN:.*]] = "llvm.sub"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SUB_NSW]], %[[SUB_NSW]], %[[SUB_PLAIN]])

// `shl` carries nsw/nuw; three flag combos must remain three ops.
^shl_flags(%k : i32, %l : i32):
    %shl_nsw_1 = "llvm.shl"(%k, %l) <{nsw}> : (i32, i32) -> i32
    %shl_nsw_2 = "llvm.shl"(%k, %l) <{nsw}> : (i32, i32) -> i32
    %shl_nuw   = "llvm.shl"(%k, %l) <{nuw}> : (i32, i32) -> i32
    %shl_plain = "llvm.shl"(%k, %l) : (i32, i32) -> i32
    "test.test"(%shl_nsw_1, %shl_nsw_2, %shl_nuw, %shl_plain) : (i32, i32, i32, i32) -> ()

    // CHECK:      %[[SHL_NSW:.*]] = "llvm.shl"(%{{.*}}, %{{.*}}) <{nsw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SHL_NUW:.*]] = "llvm.shl"(%{{.*}}, %{{.*}}) <{nuw}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SHL_PLAIN:.*]] = "llvm.shl"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SHL_NSW]], %[[SHL_NSW]], %[[SHL_NUW]], %[[SHL_PLAIN]])

// `lshr exact` is distinct from plain `lshr`.
^lshr_exact(%m : i32, %n : i32):
    %lshr_exact_1 = "llvm.lshr"(%m, %n) <{exact}> : (i32, i32) -> i32
    %lshr_exact_2 = "llvm.lshr"(%m, %n) <{exact}> : (i32, i32) -> i32
    %lshr_plain   = "llvm.lshr"(%m, %n) : (i32, i32) -> i32
    "test.test"(%lshr_exact_1, %lshr_exact_2, %lshr_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[LSHR_EXACT:.*]] = "llvm.lshr"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[LSHR_PLAIN:.*]] = "llvm.lshr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[LSHR_EXACT]], %[[LSHR_EXACT]], %[[LSHR_PLAIN]])

// `ashr exact` is distinct from plain `ashr`.
^ashr_exact(%o : i32, %p : i32):
    %ashr_exact = "llvm.ashr"(%o, %p) <{exact}> : (i32, i32) -> i32
    %ashr_plain = "llvm.ashr"(%o, %p) : (i32, i32) -> i32
    "test.test"(%ashr_exact, %ashr_plain) : (i32, i32) -> ()

    // CHECK:      %[[ASHR_EXACT:.*]] = "llvm.ashr"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ASHR_PLAIN:.*]] = "llvm.ashr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ASHR_EXACT]], %[[ASHR_PLAIN]])

// `udiv exact` and plain `udiv` are distinct; `udiv exact` duplicates merge.
// Going from "not exact" to "exact" would introduce UB where there was none
// if the dividend isn't actually divisible — keying them distinctly sidesteps
// that.
^udiv_exact(%udiv_a : i32, %udiv_b : i32):
    %udiv_exact_1 = "llvm.udiv"(%udiv_a, %udiv_b) <{exact}> : (i32, i32) -> i32
    %udiv_exact_2 = "llvm.udiv"(%udiv_a, %udiv_b) <{exact}> : (i32, i32) -> i32
    %udiv_plain   = "llvm.udiv"(%udiv_a, %udiv_b) : (i32, i32) -> i32
    "test.test"(%udiv_exact_1, %udiv_exact_2, %udiv_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[UDIV_EXACT:.*]] = "llvm.udiv"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[UDIV_PLAIN:.*]] = "llvm.udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[UDIV_EXACT]], %[[UDIV_EXACT]], %[[UDIV_PLAIN]])

// Same for `sdiv exact`.
^sdiv_exact(%sdiv_a : i32, %sdiv_b : i32):
    %sdiv_exact_1 = "llvm.sdiv"(%sdiv_a, %sdiv_b) <{exact}> : (i32, i32) -> i32
    %sdiv_exact_2 = "llvm.sdiv"(%sdiv_a, %sdiv_b) <{exact}> : (i32, i32) -> i32
    %sdiv_plain   = "llvm.sdiv"(%sdiv_a, %sdiv_b) : (i32, i32) -> i32
    "test.test"(%sdiv_exact_1, %sdiv_exact_2, %sdiv_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[SDIV_EXACT:.*]] = "llvm.sdiv"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SDIV_PLAIN:.*]] = "llvm.sdiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SDIV_EXACT]], %[[SDIV_EXACT]], %[[SDIV_PLAIN]])

// `or disjoint` is commutative and partitions identity by flag.
^or_disjoint(%q : i32, %r : i32):
    %or_disjoint_1 = "llvm.or"(%q, %r) <{disjoint}> : (i32, i32) -> i32
    %or_disjoint_2 = "llvm.or"(%r, %q) <{disjoint}> : (i32, i32) -> i32
    %or_plain      = "llvm.or"(%q, %r) : (i32, i32) -> i32
    "test.test"(%or_disjoint_1, %or_disjoint_2, %or_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[OR_DISJOINT:.*]] = "llvm.or"(%{{.*}}, %{{.*}}) <{disjoint}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[OR_PLAIN:.*]] = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[OR_DISJOINT]], %[[OR_DISJOINT]], %[[OR_PLAIN]])

// `zext nneg` is distinct from plain `zext`.
^zext_nneg(%s : i8):
    %zext_nneg_1 = "llvm.zext"(%s) <{nneg}> : (i8) -> i32
    %zext_nneg_2 = "llvm.zext"(%s) <{nneg}> : (i8) -> i32
    %zext_plain  = "llvm.zext"(%s) : (i8) -> i32
    "test.test"(%zext_nneg_1, %zext_nneg_2, %zext_plain) : (i32, i32, i32) -> ()

    // CHECK:      %[[ZEXT_NNEG:.*]] = "llvm.zext"(%{{.*}}) <{nneg}> : (i8) -> i32
    // CHECK-NEXT: %[[ZEXT_PLAIN:.*]] = "llvm.zext"(%{{.*}}) : (i8) -> i32
    // CHECK-NEXT: "test.test"(%[[ZEXT_NNEG]], %[[ZEXT_NNEG]], %[[ZEXT_PLAIN]])

// `trunc` carries nsw/nuw; three flag combos remain three ops.
^trunc_flags(%t : i64):
    %trunc_nsw  = "llvm.trunc"(%t) <{nsw}> : (i64) -> i32
    %trunc_nuw  = "llvm.trunc"(%t) <{nuw}> : (i64) -> i32
    %trunc_both_1 = "llvm.trunc"(%t) <{nuw, nsw}> : (i64) -> i32
    %trunc_both_2 = "llvm.trunc"(%t) <{nuw, nsw}> : (i64) -> i32
    "test.test"(%trunc_nsw, %trunc_nuw, %trunc_both_1, %trunc_both_2) : (i32, i32, i32, i32) -> ()

    // CHECK:      %[[TRUNC_NSW:.*]] = "llvm.trunc"(%{{.*}}) <{nsw}> : (i64) -> i32
    // CHECK-NEXT: %[[TRUNC_NUW:.*]] = "llvm.trunc"(%{{.*}}) <{nuw}> : (i64) -> i32
    // CHECK-NEXT: %[[TRUNC_BOTH:.*]] = "llvm.trunc"(%{{.*}}) <{nsw, nuw}> : (i64) -> i32
    // CHECK-NEXT: "test.test"(%[[TRUNC_NSW]], %[[TRUNC_NUW]], %[[TRUNC_BOTH]], %[[TRUNC_BOTH]])
}) : () -> ()
