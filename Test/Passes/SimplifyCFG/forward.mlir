// RUN: veir-opt %s -p=simplifycfg | filecheck %s
// RUN: veir-opt %s -p=simplifycfg,simplifycfg | filecheck %s

// Edges to blocks that contain only an unconditional branch are redirected to
// that branch's destination. Bypassed blocks become dead and are erased.

"builtin.module"() ({
  // Forward a whole chain, keeping the branch's properties and attributes, and
  // stop at a block with an ordinary instruction.
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

  // Substitute block arguments through permutations, duplication, drops, and
  // values captured from the enclosing scope. Each edge keeps its own values.
  "llvm.func"() <{sym_name = "arguments", function_type = !llvm.func<i32 (i1, i32, i32)>}> ({
  ^entry(%cond : i1, %a : i32, %b : i32):
    "cf.cond_br"(%cond, %a, %b, %b, %a) [^swap, ^swap] <{operandSegmentSizes = array<i32: 1, 2, 2>}> : (i1, i32, i32, i32, i32) -> ()
  ^swap(%x : i32, %y : i32):
    "cf.br"(%y, %x, %y) [^drop] : (i32, i32, i32) -> ()
  ^drop(%p : i32, %q : i32, %r : i32):
    "cf.br"(%p, %r, %a, %q) [^exit] : (i32, i32, i32, i32) -> ()
  ^exit(%v : i32, %w : i32, %u : i32, %t : i32):
    %sum = "arith.addi"(%v, %w) : (i32, i32) -> i32
    "llvm.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // Bypassing ^empty would leave %x undefined at its use in ^exit.
  "llvm.func"() <{sym_name = "external_use", function_type = !llvm.func<i32 (i32)>}> ({
  ^entry(%a : i32):
    "llvm.br"(%a) [^empty] : (i32) -> ()
  ^empty(%x : i32):
    "llvm.br"() [^exit] : () -> ()
  ^exit:
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()

  // The two-operand RISC-V comparisons keep both leading operands.
  "llvm.func"() <{sym_name = "riscv", function_type = !llvm.func<!riscv.reg (!riscv.reg, !riscv.reg)>}> ({
  ^entry(%a : !riscv.reg, %b : !riscv.reg):
    "riscv_cf.beq"(%a, %b, %a) [^empty, ^exit] <{operandSegmentSizes = array<i32: 1, 1, 1, 0>}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  ^empty(%x : !riscv.reg):
    "riscv_cf.branch"() [^exit] : () -> ()
  ^exit:
    "llvm.return"(%a) : (!riscv.reg) -> ()
  }) : () -> ()

  "cir.func"() <{sym_name = "cir", function_type = !cir.func<(!cir.bool, !cir.int<s, 32>) -> !cir.int<s, 32>>}> ({
  ^entry(%cond : !cir.bool, %a : !cir.int<s, 32>):
    "cir.brcond"(%cond, %a) [^empty, ^exit] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (!cir.bool, !cir.int<s, 32>) -> ()
  ^empty(%x : !cir.int<s, 32>):
    "cir.br"() [^exit] : () -> ()
  ^exit:
    "cir.return"(%a) : (!cir.int<s, 32>) -> ()
  }) : () -> ()

  // Chains that cycle are left alone.
  "llvm.func"() <{sym_name = "self_loop", function_type = !llvm.func<void ()>}> ({
  ^entry:
    "llvm.br"() [^loop] : () -> ()
  ^loop:
    "llvm.br"() [^loop] : () -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "cycle", function_type = !llvm.func<void (i32, i32)>}> ({
  ^entry(%a : i32, %b : i32):
    "llvm.br"(%a, %b) [^one] : (i32, i32) -> ()
  ^one(%x : i32, %y : i32):
    "llvm.br"(%y, %x) [^two] : (i32, i32) -> ()
  ^two(%p : i32, %q : i32):
    "llvm.br"(%p, %q) [^one] : (i32, i32) -> ()
  }) : () -> ()

  // A backedge through an empty block is forwarded to the loop header.
  "llvm.func"() <{sym_name = "backedge", function_type = !llvm.func<void (i32)>}> ({
  ^entry(%a : i32):
    "llvm.br"(%a) [^loop] : (i32) -> ()
  ^loop(%x : i32):
    %sum = "llvm.add"(%x, %x) : (i32, i32) -> i32
    "llvm.br"(%sum) [^latch] : (i32) -> ()
  ^latch(%y : i32):
    "llvm.br"(%y) [^loop] : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "chain"
// CHECK: "llvm.cond_br"(%{{.*}}) [^[[EXIT:[0-9]+]], ^[[EXIT]]] <{"branch_weights" = array<i32: 3, 7>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> {"test.tag" = "keep"}
// CHECK-NEXT: ^[[EXIT]]():
// CHECK-NEXT: %[[SUM:[0-9]+]] = "llvm.add"
// CHECK-NEXT: "llvm.br"() [^[[RET:[0-9]+]]]
// CHECK-NEXT: ^[[RET]]():
// CHECK-NEXT: "llvm.return"(%[[SUM]])
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "arguments"
// CHECK: ^{{[0-9]+}}(%[[COND:[a-z0-9_]+]] : i1, %[[A:[a-z0-9_]+]] : i32, %[[B:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "cf.cond_br"(%[[COND]], %[[B]], %[[B]], %[[A]], %[[A]], %[[A]], %[[A]], %[[A]], %[[B]]) [^[[EXIT:[0-9]+]], ^[[EXIT]]] <{"operandSegmentSizes" = array<i32: 1, 4, 4>}>
// CHECK-NEXT: ^[[EXIT]](
// CHECK-NEXT: "arith.addi"
// CHECK-NEXT: "llvm.return"
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "external_use"
// CHECK: "llvm.br"(%{{[a-z0-9_]+}}) [^[[EMPTY:[0-9]+]]]
// CHECK-NEXT: ^[[EMPTY]](%[[ARG:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.br"() [^[[USE:[0-9]+]]]
// CHECK-NEXT: ^[[USE]]():
// CHECK-NEXT: "llvm.return"(%[[ARG]])

// CHECK-LABEL: "sym_name" = "riscv"
// CHECK: ^{{[0-9]+}}(%[[A:[a-z0-9_]+]] : !riscv.reg, %[[B:[a-z0-9_]+]] : !riscv.reg):
// CHECK-NEXT: "riscv_cf.beq"(%[[A]], %[[B]]) [^[[EXIT:[0-9]+]], ^[[EXIT]]] <{"operandSegmentSizes" = array<i32: 1, 1, 0, 0>}>
// CHECK-NEXT: ^[[EXIT]]():
// CHECK-NEXT: "llvm.return"(%[[A]])
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "cir"
// CHECK: ^{{[0-9]+}}(%[[COND:[a-z0-9_]+]] : !cir.bool, %{{[a-z0-9_]+}} : !cir.int<s, 32>):
// CHECK-NEXT: "cir.brcond"(%[[COND]]) [^[[EXIT:[0-9]+]], ^[[EXIT]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}>
// CHECK-NEXT: ^[[EXIT]]():
// CHECK-NEXT: "cir.return"
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "self_loop"
// CHECK: "llvm.br"() [^[[SELF:[0-9]+]]]
// CHECK-NEXT: ^[[SELF]]():
// CHECK-NEXT: "llvm.br"() [^[[SELF]]]

// CHECK-LABEL: "sym_name" = "cycle"
// CHECK: "llvm.br"(%{{[a-z0-9_]+}}, %{{[a-z0-9_]+}}) [^[[ONE:[0-9]+]]]
// CHECK-NEXT: ^[[ONE]](%[[X:[a-z0-9_]+]] : i32, %[[Y:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.br"(%[[Y]], %[[X]]) [^[[TWO:[0-9]+]]]
// CHECK-NEXT: ^[[TWO]](%[[P:[a-z0-9_]+]] : i32, %[[Q:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.br"(%[[P]], %[[Q]]) [^[[ONE]]]

// CHECK-LABEL: "sym_name" = "backedge"
// CHECK: "llvm.br"(%{{[a-z0-9_]+}}) [^[[LOOP:[0-9]+]]]
// CHECK-NEXT: ^[[LOOP]](%[[VALUE:[a-z0-9_]+]] : i32):
// CHECK-NEXT: %[[SUM:[0-9]+]] = "llvm.add"(%[[VALUE]], %[[VALUE]])
// CHECK-NEXT: "llvm.br"(%[[SUM]]) [^[[LOOP]]]
// CHECK-NEXT: }) : () -> ()
