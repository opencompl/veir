// RUN: veir-opt %s -p=simplifycfg | filecheck %s

// Conditional branches on constants become unconditional branches to the
// successor they take, forwarding that successor's operands.

"builtin.module"() ({
  // Branch weights are properties of the conditional branch and are dropped;
  // discardable attributes are kept. The untaken successor becomes dead.
  "llvm.func"() <{sym_name = "llvm_true", function_type = !llvm.func<i32 (i32, i32)>}> ({
  ^entry(%a : i32, %b : i32):
    %c = "llvm.mlir.constant"() <{value = true}> : () -> i1
    "llvm.cond_br"(%c, %a, %b) [^t, ^f] <{operandSegmentSizes = array<i32: 1, 1, 1>, branch_weights = array<i32: 3, 7>}> {test.tag = "keep"} : (i1, i32, i32) -> ()
  ^t(%x : i32):
    "llvm.return"(%x) : (i32) -> ()
  ^f(%y : i32):
    %z = "llvm.add"(%y, %y) : (i32, i32) -> i32
    "llvm.return"(%z) : (i32) -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "cf_false", function_type = !llvm.func<i32 (i32, i32)>}> ({
  ^entry(%a : i32, %b : i32):
    %c = "arith.constant"() <{value = 0 : i1}> : () -> i1
    "cf.cond_br"(%c, %a, %b) [^t, ^f] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^t(%x : i32):
    "llvm.return"(%x) : (i32) -> ()
  ^f(%y : i32):
    %z = "arith.addi"(%y, %y) : (i32, i32) -> i32
    "llvm.return"(%z) : (i32) -> ()
  }) : () -> ()

  // The taken edge is identified even when both successors are the same block:
  // 2 <u 1 is false, so %one's edge is taken.
  "llvm.func"() <{sym_name = "riscv_same_successor", function_type = !llvm.func<!riscv.reg ()>}> ({
  ^entry:
    %one = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
    %two = "riscv.li"() <{value = 2 : i64}> : () -> !riscv.reg
    "riscv_cf.bltu"(%two, %one, %two, %one) [^exit, ^exit] <{operandSegmentSizes = array<i32: 1, 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  ^exit(%r : !riscv.reg):
    "llvm.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "riscv_bnez", function_type = !llvm.func<void ()>}> ({
  ^entry:
    %zero = "riscv.li"() <{value = 0 : i64}> : () -> !riscv.reg
    "riscv_cf.bnez"(%zero) [^t, ^f] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
  ^t:
    "llvm.return"() : () -> ()
  ^f:
    "llvm.unreachable"() : () -> ()
  }) : () -> ()

  // Branching on poison is UB; leave it for other passes.
  "llvm.func"() <{sym_name = "poison", function_type = !llvm.func<void ()>}> ({
  ^entry:
    %p = "llvm.mlir.poison"() : () -> i1
    "llvm.cond_br"(%p) [^t, ^f] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^t:
    "llvm.return"() : () -> ()
  ^f:
    "llvm.unreachable"() : () -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "unknown", function_type = !llvm.func<void (i1)>}> ({
  ^entry(%c : i1):
    "llvm.cond_br"(%c) [^t, ^f] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^t:
    "llvm.return"() : () -> ()
  ^f:
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "llvm_true"
// CHECK: ^{{[0-9]+}}(%[[A:[a-z0-9_]+]] : i32, %{{[a-z0-9_]+}} : i32):
// CHECK: "llvm.br"(%[[A]]) [^[[T:[0-9]+]]] {"test.tag" = "keep"} : (i32) -> ()
// CHECK-NEXT: ^[[T]](%[[X:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.return"(%[[X]])
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "cf_false"
// CHECK: ^{{[0-9]+}}(%{{[a-z0-9_]+}} : i32, %[[B:[a-z0-9_]+]] : i32):
// CHECK: "cf.br"(%[[B]]) [^[[F:[0-9]+]]] : (i32) -> ()
// CHECK-NEXT: ^[[F]](%[[Y:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "arith.addi"(%[[Y]], %[[Y]])
// CHECK-NEXT: "llvm.return"
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "riscv_same_successor"
// CHECK: %[[ONE:[0-9]+]] = "riscv.li"() <{"value" = 1 : i64}>
// CHECK: "riscv_cf.branch"(%[[ONE]]) [^[[EXIT:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT: ^[[EXIT]](

// CHECK-LABEL: "sym_name" = "riscv_bnez"
// CHECK: "riscv_cf.branch"() [^[[F:[0-9]+]]] : () -> ()
// CHECK-NEXT: ^[[F]]():
// CHECK-NEXT: "llvm.unreachable"
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "poison"
// CHECK: "llvm.cond_br"
// CHECK: "llvm.return"
// CHECK: "llvm.unreachable"

// CHECK-LABEL: "sym_name" = "unknown"
// CHECK: "llvm.cond_br"
// CHECK: "llvm.return"
// CHECK: "llvm.unreachable"
