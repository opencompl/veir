// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// `llvm.br` becomes `gmir.g_br` and `llvm.cond_br` becomes `gmir.g_brcond`, with the same
// successors and forwarded operands. Branch weights are dropped.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i64 (i1, i64, i32)>}> ({
  ^bb0(%c: i1, %x: i64, %y: i32):
    "llvm.cond_br"(%c, %x, %y) [^bb1, ^bb2] <{branch_weights = array<i32: 3, 1>, operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i32) -> ()
  ^bb1(%a: i64):
    "llvm.br"(%a) [^bb3] : (i64) -> ()
  ^bb2(%b: i32):
    "llvm.br"(%x) [^bb3] : (i64) -> ()
  ^bb3(%r: i64):
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[C:.*]] : i1, %[[X:.*]] : i64, %[[Y:.*]] : i32):
// CHECK-NEXT:   "gmir.g_brcond"(%[[C]], %[[X]], %[[Y]]) [^[[BB1:.*]], ^[[BB2:.*]]] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i64, i32) -> ()
// CHECK-NEXT: ^[[BB1]](%[[A:.*]] : i64):
// CHECK-NEXT:   "gmir.g_br"(%[[A]]) [^[[BB3:.*]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB2]](%{{.*}} : i32):
// CHECK-NEXT:   "gmir.g_br"(%[[X]]) [^[[BB3]]] : (i64) -> ()
// CHECK-NEXT: ^[[BB3]](%[[R:.*]] : i64):
// CHECK-NEXT:   "llvm.return"(%[[R]]) : (i64) -> ()
