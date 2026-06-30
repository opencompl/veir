// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({

  // Positive case: a dominating definition is reused in a dominated block.
  // %a0 in ^bb0 dominates the recomputation in ^bb1, so the recomputation is
  // eliminated and its use is rewired to %a0.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>}> ({
  ^bb0(%arg0 : i32, %arg1 : i32):
    %a0 = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%a0) : (i32) -> ()
    "llvm.br"() [^bb1] : () -> ()
  ^bb1:
    %a1 = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%a1) : (i32) -> ()
    "llvm.return"() : () -> ()

    // CHECK-LABEL: void (i32, i32)>
    // CHECK: %[[A:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[A]]) : (i32) -> ()
    // CHECK: ^{{[0-9]+}}():
    // CHECK-NEXT: "test.test"(%[[A]]) : (i32) -> ()
    // CHECK-NEXT: "llvm.return"() : () -> ()
  }) : () -> ()

  // Negative case: sibling branches of a diamond do not dominate each other,
  // so the equivalent expression computed in each branch must be kept.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32, i1)>}> ({
  ^bb0(%arg0 : i32, %arg1 : i32, %cond : i1):
    "llvm.cond_br"(%cond) [^bb1, ^bb2] <{branch_weights = array<i32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    %l = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%l) : (i32) -> ()
    "llvm.br"() [^bb3] : () -> ()
  ^bb2:
    %r = "llvm.add"(%arg0, %arg1) : (i32, i32) -> i32
    "test.test"(%r) : (i32) -> ()
    "llvm.br"() [^bb3] : () -> ()
  ^bb3:
    "llvm.return"() : () -> ()

    // Each sibling keeps its own add.
    // CHECK-LABEL: void (i32, i32, i1)>
    // CHECK: ^{{[0-9]+}}():
    // CHECK-NEXT: %[[L:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[L]]) : (i32) -> ()
    // CHECK: ^{{[0-9]+}}():
    // CHECK-NEXT: %[[R:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
    // CHECK-NEXT: "test.test"(%[[R]]) : (i32) -> ()
  }) : () -> ()

}) : () -> ()
