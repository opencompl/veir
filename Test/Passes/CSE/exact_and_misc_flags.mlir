// RUN: veir-opt %s -p=cse | filecheck %s

// Tests that the CSE pass treats exact/disjoint/nneg flags as part of an
// operation's identity.

"builtin.module"() ({
  "llvm.func"() ({

// `lshr exact` is distinct from plain `lshr`.
^lshr_exact(%m : i32, %n : i32):
    %lshr_exact_1 = "llvm.lshr"(%m, %n) <{exact}> : (i32, i32) -> i32
    %lshr_exact_2 = "llvm.lshr"(%m, %n) <{exact}> : (i32, i32) -> i32
    %lshr_plain   = "llvm.lshr"(%m, %n) : (i32, i32) -> i32
    "test.test"(%lshr_exact_1, %lshr_exact_2, %lshr_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[LSHR_EXACT:.*]] = "llvm.lshr"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[LSHR_PLAIN:.*]] = "llvm.lshr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[LSHR_EXACT]], %[[LSHR_EXACT]], %[[LSHR_PLAIN]])

// `ashr exact` is distinct from plain `ashr`.
    "llvm.return"() : () -> ()
^ashr_exact(%o : i32, %p : i32):
    %ashr_exact = "llvm.ashr"(%o, %p) <{exact}> : (i32, i32) -> i32
    %ashr_plain = "llvm.ashr"(%o, %p) : (i32, i32) -> i32
    "test.test"(%ashr_exact, %ashr_plain) : (i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[ASHR_EXACT:.*]] = "llvm.ashr"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[ASHR_PLAIN:.*]] = "llvm.ashr"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[ASHR_EXACT]], %[[ASHR_PLAIN]])

// `udiv exact` and plain `udiv` are distinct; `udiv exact` duplicates merge.
// Going from "not exact" to "exact" would introduce UB where there was none
// if the dividend isn't actually divisible - keying them distinctly sidesteps
// that.
    "llvm.return"() : () -> ()
^udiv_exact(%udiv_a : i32, %udiv_b : i32):
    %udiv_exact_1 = "llvm.udiv"(%udiv_a, %udiv_b) <{exact}> : (i32, i32) -> i32
    %udiv_exact_2 = "llvm.udiv"(%udiv_a, %udiv_b) <{exact}> : (i32, i32) -> i32
    %udiv_plain   = "llvm.udiv"(%udiv_a, %udiv_b) : (i32, i32) -> i32
    "test.test"(%udiv_exact_1, %udiv_exact_2, %udiv_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[UDIV_EXACT:.*]] = "llvm.udiv"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[UDIV_PLAIN:.*]] = "llvm.udiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[UDIV_EXACT]], %[[UDIV_EXACT]], %[[UDIV_PLAIN]])

// Same for `sdiv exact`.
    "llvm.return"() : () -> ()
^sdiv_exact(%sdiv_a : i32, %sdiv_b : i32):
    %sdiv_exact_1 = "llvm.sdiv"(%sdiv_a, %sdiv_b) <{exact}> : (i32, i32) -> i32
    %sdiv_exact_2 = "llvm.sdiv"(%sdiv_a, %sdiv_b) <{exact}> : (i32, i32) -> i32
    %sdiv_plain   = "llvm.sdiv"(%sdiv_a, %sdiv_b) : (i32, i32) -> i32
    "test.test"(%sdiv_exact_1, %sdiv_exact_2, %sdiv_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[SDIV_EXACT:.*]] = "llvm.sdiv"(%{{.*}}, %{{.*}}) <{exact}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[SDIV_PLAIN:.*]] = "llvm.sdiv"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[SDIV_EXACT]], %[[SDIV_EXACT]], %[[SDIV_PLAIN]])

// `or disjoint` is commutative and partitions identity by flag.
    "llvm.return"() : () -> ()
^or_disjoint(%q : i32, %r : i32):
    %or_disjoint_1 = "llvm.or"(%q, %r) <{disjoint}> : (i32, i32) -> i32
    %or_disjoint_2 = "llvm.or"(%r, %q) <{disjoint}> : (i32, i32) -> i32
    %or_plain      = "llvm.or"(%q, %r) : (i32, i32) -> i32
    "test.test"(%or_disjoint_1, %or_disjoint_2, %or_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i32, %{{.*}} : i32):
    // CHECK-NEXT: %[[OR_DISJOINT:.*]] = "llvm.or"(%{{.*}}, %{{.*}}) <{disjoint}> : (i32, i32) -> i32
    // CHECK-NEXT: %[[OR_PLAIN:.*]] = "llvm.or"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[OR_DISJOINT]], %[[OR_DISJOINT]], %[[OR_PLAIN]])

// `zext nneg` is distinct from plain `zext`.
    "llvm.return"() : () -> ()
^zext_nneg(%s : i8):
    %zext_nneg_1 = "llvm.zext"(%s) <{nneg}> : (i8) -> i32
    %zext_nneg_2 = "llvm.zext"(%s) <{nneg}> : (i8) -> i32
    %zext_plain  = "llvm.zext"(%s) : (i8) -> i32
    "test.test"(%zext_nneg_1, %zext_nneg_2, %zext_plain) : (i32, i32, i32) -> ()

    // CHECK-LABEL: ^{{.*}}(%{{.*}} : i8):
    // CHECK-NEXT: %[[ZEXT_NNEG:.*]] = "llvm.zext"(%{{.*}}) <{nneg}> : (i8) -> i32
    // CHECK-NEXT: %[[ZEXT_PLAIN:.*]] = "llvm.zext"(%{{.*}}) : (i8) -> i32
    // CHECK-NEXT: "test.test"(%[[ZEXT_NNEG]], %[[ZEXT_NNEG]], %[[ZEXT_PLAIN]])
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
