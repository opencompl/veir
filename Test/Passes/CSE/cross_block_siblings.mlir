// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

"builtin.module"() ({
  // A candidate from the left sibling is encountered first but does not dominate
  // the right sibling. The first add in ^right must become a candidate so the
  // second add in ^right, and the add in ^right_child, can reuse it.
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32, i1)>}> ({
  ^entry(%a : i32, %b : i32, %cond : i1):
    "llvm.cond_br"(%cond) [^left, ^right] <{branch_weights = array<i32>, operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^left:
    %l = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%l) : (i32) -> ()
    "llvm.return"() : () -> ()
  ^right:
    %r1 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%r1) : (i32) -> ()
    %r2 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%r2) : (i32) -> ()
    "llvm.br"() [^right_child] : () -> ()
  ^right_child:
    %r3 = "llvm.add"(%a, %b) : (i32, i32) -> i32
    "test.test"(%r3) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()

  // CHECK-LABEL: void (i32, i32, i1)>
  // CHECK:       ^{{[0-9]+}}(%{{.*}} : i32, %{{.*}} : i32, %{{.*}} : i1):
  // CHECK-NEXT:    "llvm.cond_br"
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    %[[L:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[L]]) : (i32) -> ()
  // CHECK-NEXT:    "llvm.return"() : () -> ()
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    %[[R:.*]] = "llvm.add"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
  // CHECK-NEXT:    "test.test"(%[[R]]) : (i32) -> ()
  // CHECK-NEXT:    "test.test"(%[[R]]) : (i32) -> ()
  // CHECK-NEXT:    "llvm.br"() [^{{[0-9]+}}] : () -> ()
  // CHECK:       ^{{[0-9]+}}():
  // CHECK-NEXT:    "test.test"(%[[R]]) : (i32) -> ()
  // CHECK-NEXT:    "llvm.return"() : () -> ()
}) : () -> ()
