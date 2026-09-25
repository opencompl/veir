// RUN: veir-opt %s -p=simplifycfg | filecheck %s

// Blocks unreachable from their region's entry block are erased.

"builtin.module"() ({
  // A dead loop whose values flow between its blocks, including a value from
  // one dead block used in another.
  "llvm.func"() <{sym_name = "dead_loop", function_type = !llvm.func<i32 (i32)>}> ({
  ^entry(%a : i32):
    "llvm.return"(%a) : (i32) -> ()
  ^one:
    %v = "llvm.add"(%a, %a) : (i32, i32) -> i32
    "llvm.br"(%v) [^two] : (i32) -> ()
  ^two(%x : i32):
    %y = "llvm.add"(%x, %v) : (i32, i32) -> i32
    "llvm.br"() [^one] : () -> ()
  }) : () -> ()

  // Dead blocks between live ones.
  "llvm.func"() <{sym_name = "interleaved", function_type = !llvm.func<void (i1)>}> ({
  ^entry(%c : i1):
    "llvm.cond_br"(%c) [^a, ^b] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^dead1:
    "llvm.br"() [^a] : () -> ()
  ^a:
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.return"() : () -> ()
  ^dead2:
    "llvm.br"() [^b] : () -> ()
  ^b:
    %two = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()

  // Dead operations that use each other's results cyclically (legal only in
  // unreachable code) cannot be erased one at a time, so the region's dead
  // blocks are kept.
  "llvm.func"() <{sym_name = "dead_cycle", function_type = !llvm.func<void ()>}> ({
  ^entry:
    "llvm.return"() : () -> ()
  ^dead:
    %p = "llvm.add"(%q, %q) : (i32, i32) -> i32
    %q = "llvm.add"(%p, %p) : (i32, i32) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "dead_loop"
// CHECK-NEXT: ^{{[0-9]+}}(%[[A:[a-z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.return"(%[[A]])
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "interleaved"
// CHECK-NEXT: ^{{[0-9]+}}(%{{[a-z0-9_]+}} : i1):
// CHECK-NEXT: "llvm.cond_br"(%{{[a-z0-9_]+}}) [^[[A:[0-9]+]], ^[[B:[0-9]+]]]
// CHECK-NEXT: ^[[A]]():
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 1 : i32}>
// CHECK-NEXT: "llvm.return"
// CHECK-NEXT: ^[[B]]():
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 2 : i32}>
// CHECK-NEXT: "llvm.return"
// CHECK-NEXT: }) : () -> ()

// CHECK-LABEL: "sym_name" = "dead_cycle"
// CHECK: "llvm.return"
// CHECK-NEXT: ^{{[0-9]+}}():
// CHECK-NEXT: "llvm.add"
// CHECK-NEXT: "llvm.add"
// CHECK-NEXT: "llvm.return"
