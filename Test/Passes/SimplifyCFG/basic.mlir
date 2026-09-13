// RUN: veir-opt %s -p=simplifycfg | filecheck %s
// RUN: veir-opt %s -p=simplifycfg,simplifycfg | filecheck %s

"builtin.module"() ({
  // Forward an entire chain and both edges to the same destination. Keep the
  // bypassed blocks, and stop at the block containing an ordinary instruction.
  "llvm.func"() <{sym_name = "chain", function_type = !llvm.func<i32 (i1, i32)>}> ({
  ^entry(%cond : i1, %x : i32):
    "llvm.cond_br"(%cond) [^left, ^right] <{operandSegmentSizes = array<i32: 1, 0, 0>, branch_weights = array<i32: 3, 7>}> {test.tag = "keep"} : (i1) -> ()
  ^left:
    "llvm.br"() [^middle] : () -> ()
  ^middle:
    "llvm.br"() [^exit] : () -> ()
  ^right:
    "llvm.br"() [^exit] : () -> ()
  ^exit:
    %sum = "llvm.add"(%x, %x) : (i32, i32) -> i32
    "llvm.br"() [^ret] : () -> ()
  ^ret:
    "llvm.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // A block containing only a conditional branch is not a forwarding block.
  "llvm.func"() <{sym_name = "conditional", function_type = !llvm.func<void (i1)>}> ({
  ^entry(%cond : i1):
    "llvm.br"() [^branch] : () -> ()
  ^branch:
    "llvm.cond_br"(%cond) [^left, ^right] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^left:
    "llvm.return"() : () -> ()
  ^right:
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "chain"
// CHECK: "llvm.cond_br"(%{{.*}}) [^[[EXIT:[0-9]+]], ^[[EXIT]]] <{"branch_weights" = array<i32: 3, 7>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> {"test.tag" = "keep"}
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: "llvm.br"() [^[[EXIT]]]
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: "llvm.br"() [^[[EXIT]]]
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: "llvm.br"() [^[[EXIT]]]
// CHECK-NEXT: ^[[EXIT]]():
// CHECK-NEXT: %[[SUM:[0-9]+]] = "llvm.add"
// CHECK-NEXT: "llvm.br"() [^[[RET:[0-9]+]]]
// CHECK-NEXT: ^[[RET]]():
// CHECK-NEXT: "llvm.return"(%[[SUM]])

// CHECK-LABEL: "sym_name" = "conditional"
// CHECK: "llvm.br"() [^[[BRANCH:[0-9]+]]]
// CHECK-NEXT: ^[[BRANCH]]():
// CHECK-NEXT: "llvm.cond_br"
