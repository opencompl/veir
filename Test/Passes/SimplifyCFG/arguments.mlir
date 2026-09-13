// RUN: veir-opt %s -p=simplifycfg | filecheck %s
// RUN: veir-opt %s -p=simplifycfg,simplifycfg | filecheck %s

"builtin.module"() ({
  // Compose permutations, duplication, and captured values across a chain.
  // Each conditional edge retains its own values even with a shared target.
  "llvm.func"() <{sym_name = "arguments", function_type = !llvm.func<i32 (i1, i32, i32)>}> ({
  ^entry(%cond : i1, %a : i32, %b : i32):
    "cf.cond_br"(%cond, %a, %b, %b, %a) [^swap, ^swap] <{operandSegmentSizes = array<i32: 1, 2, 2>, branch_weights = array<i32: 9, 1>}> : (i1, i32, i32, i32, i32) -> ()
  ^swap(%x : i32, %y : i32):
    "cf.br"(%y, %x, %y) [^drop] : (i32, i32, i32) -> ()
  ^drop(%p : i32, %q : i32, %r : i32):
    "cf.br"(%p, %r, %a, %q) [^exit] : (i32, i32, i32, i32) -> ()
  ^exit(%v : i32, %w : i32, %u : i32, %t : i32):
    %sum = "llvm.add"(%v, %w) : (i32, i32) -> i32
    "llvm.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // Dropping every argument updates the direct branch's operand list too.
  "llvm.func"() <{sym_name = "drop", function_type = !llvm.func<void (i32)>}> ({
  ^entry(%a : i32):
    "llvm.br"(%a) [^empty] : (i32) -> ()
  ^empty(%unused : i32):
    "llvm.br"() [^exit] : () -> ()
  ^exit:
    "llvm.return"() : () -> ()
  }) : () -> ()

  // Bypassing this block would leave %x undefined at its use in the return.
  "llvm.func"() <{sym_name = "external_use", function_type = !llvm.func<i32 (i32)>}> ({
  ^entry(%a : i32):
    "llvm.br"(%a) [^empty] : (i32) -> ()
  ^empty(%x : i32):
    "llvm.br"() [^exit] : () -> ()
  ^exit:
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "arguments"
// CHECK: ^{{[a-zA-Z0-9_]+}}(%[[COND:[a-zA-Z0-9_]+]] : i1, %[[A:[a-zA-Z0-9_]+]] : i32, %[[B:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "cf.cond_br"(%[[COND]], %[[B]], %[[B]], %[[A]], %[[A]], %[[A]], %[[A]], %[[A]], %[[B]]) [^[[EXIT:[a-zA-Z0-9_]+]], ^[[EXIT]]] <{"branch_weights" = array<i32: 9, 1>, "operandSegmentSizes" = array<i32: 1, 4, 4>}>
// CHECK: ^{{[a-zA-Z0-9_]+}}(%[[X:[a-zA-Z0-9_]+]] : i32, %[[Y:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "cf.br"(%[[Y]], %[[Y]], %[[A]], %[[X]]) [^[[EXIT]]]
// CHECK: ^[[EXIT]](
// CHECK-NEXT: %{{[a-zA-Z0-9_]+}} = "llvm.add"

// CHECK-LABEL: "sym_name" = "drop"
// CHECK: "llvm.br"() [^[[DROP_EXIT:[a-zA-Z0-9_]+]]] : () -> ()
// CHECK: ^[[DROP_EXIT]]():
// CHECK-NEXT: "llvm.return"()

// CHECK-LABEL: "sym_name" = "external_use"
// CHECK: "llvm.br"(%{{[a-zA-Z0-9_]+}}) [^[[EMPTY:[a-zA-Z0-9_]+]]]
// CHECK-NEXT: ^[[EMPTY]](%[[ARG:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.br"() [^[[USE_EXIT:[a-zA-Z0-9_]+]]]
// CHECK-NEXT: ^[[USE_EXIT]]():
// CHECK-NEXT: "llvm.return"(%[[ARG]])
