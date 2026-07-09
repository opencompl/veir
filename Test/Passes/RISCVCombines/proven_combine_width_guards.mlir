// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// The seven combines that carry a graph-level `PreservesSemantics` proof
// (`Veir/Passes/RISCVCombines/CombineSemantics.lean`) are guarded to the integer widths at
// which their `veir_bv_decide` data lemmas are stated: `i32`/`i64` (and `i32 -> i64 -> i32`
// for `trunc_of_zext`). `bv_decide` bitblasts, so it cannot discharge a width-generic goal;
// the guard is what lets the proof reach the data lemma. This test pins that the rewrites
// still fire at the proven widths and deliberately do not fire below them.

"builtin.module"() ({
  // select_same_val_self at i64: fires.
  "func.func"() <{function_type = (i1, i64) -> i64}> ({
  ^bb0(%c: i1, %x: i64):
    %r = "llvm.select"(%c, %x, %x) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // select_same_val_self at i8: guarded off.
  "func.func"() <{function_type = (i1, i8) -> i8}> ({
  ^bb0(%c: i1, %x: i8):
    %r = "llvm.select"(%c, %x, %x) : (i1, i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // sub_add_reg_x_add_y_sub_y at i64: fires.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %a = "llvm.add"(%x, %y) : (i64, i64) -> i64
    %r = "llvm.sub"(%a, %y) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // sub_add_reg_x_add_y_sub_y at i8: guarded off.
  "func.func"() <{function_type = (i8, i8) -> i8}> ({
  ^bb0(%x: i8, %y: i8):
    %a = "llvm.add"(%x, %y) : (i8, i8) -> i8
    %r = "llvm.sub"(%a, %y) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // mulo_by_2 at i32: fires (the op-creating exemplar).
  "func.func"() <{function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %c2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %r = "llvm.mul"(%x, %c2) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // mulo_by_2 at i8: guarded off.
  "func.func"() <{function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %c2 = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %r = "llvm.mul"(%x, %c2) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // trunc_of_zext at i8 -> i16 -> i8: guarded off (only i32 -> i64 -> i32 is proven).
  "func.func"() <{function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %z = "llvm.zext"(%x) : (i8) -> i16
    %t = "llvm.trunc"(%z) : (i16) -> i8
    "func.return"(%t) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// select_same_val_self, i64: the select is gone, %x is returned directly.
// CHECK:      ^{{.*}}(%{{.*}} : i1, %[[X:.*]] : i64):
// CHECK-NOT:  "llvm.select"
// CHECK:      "func.return"(%[[X]]) : (i64) -> ()

// select_same_val_self, i8: the select survives.
// CHECK:      ^{{.*}}(%{{.*}} : i1, %[[SX:.*]] : i8):
// CHECK:      %[[SR:.*]] = "llvm.select"(%{{.*}}, %[[SX]], %[[SX]]) : (i1, i8, i8) -> i8
// CHECK:      "func.return"(%[[SR]]) : (i8) -> ()

// sub_add_reg, i64: the sub is gone, %x is returned directly.
// CHECK:      ^{{.*}}(%[[AX:.*]] : i64, %{{.*}} : i64):
// CHECK-NOT:  "llvm.sub"
// CHECK:      "func.return"(%[[AX]]) : (i64) -> ()

// sub_add_reg, i8: the sub survives.
// CHECK:      ^{{.*}}(%{{.*}} : i8, %[[BY:.*]] : i8):
// CHECK:      %[[BR:.*]] = "llvm.sub"(%{{.*}}, %[[BY]]) : (i8, i8) -> i8
// CHECK:      "func.return"(%[[BR]]) : (i8) -> ()

// mulo_by_2, i32: rewritten to an add.
// CHECK:      ^{{.*}}(%[[MX:.*]] : i32):
// CHECK:      %[[MR:.*]] = "llvm.add"(%[[MX]], %[[MX]]) : (i32, i32) -> i32
// CHECK:      "func.return"(%[[MR]]) : (i32) -> ()

// mulo_by_2, i8: the mul survives.
// CHECK:      ^{{.*}}(%[[NX:.*]] : i8):
// CHECK:      %[[NR:.*]] = "llvm.mul"(%[[NX]],
// CHECK:      "func.return"(%[[NR]]) : (i8) -> ()

// trunc_of_zext, i8 -> i16 -> i8: both casts survive.
// CHECK:      ^{{.*}}(%[[TX:.*]] : i8):
// CHECK:      %[[TZ:.*]] = "llvm.zext"(%[[TX]]) : (i8) -> i16
// CHECK:      %[[TT:.*]] = "llvm.trunc"(%[[TZ]]) : (i16) -> i8
// CHECK:      "func.return"(%[[TT]]) : (i8) -> ()
