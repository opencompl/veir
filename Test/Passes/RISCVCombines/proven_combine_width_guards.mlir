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

  // trunc_of_zext at i8 -> i16 -> i8: guarded off (only i32 -> i64 -> i32 is proven).
  "func.func"() <{function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %z = "llvm.zext"(%x) : (i8) -> i16
    %t = "llvm.trunc"(%z) : (i16) -> i8
    "func.return"(%t) : (i8) -> ()
  }) : () -> ()

  // select_to_iminmax_ugt at i64: fires (predicate 8 = ugt).
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %c = "llvm.icmp"(%x, %y) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %r = "llvm.select"(%c, %x, %y) : (i1, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // select_to_iminmax_ugt at i8: guarded off.
  "func.func"() <{function_type = (i8, i8) -> i8}> ({
  ^bb0(%x: i8, %y: i8):
    %c = "llvm.icmp"(%x, %y) <{predicate = 8 : i64}> : (i8, i8) -> i1
    %r = "llvm.select"(%c, %x, %y) : (i1, i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
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

// trunc_of_zext, i8 -> i16 -> i8: both casts survive.
// CHECK:      ^{{.*}}(%[[TX:.*]] : i8):
// CHECK:      %[[TZ:.*]] = "llvm.zext"(%[[TX]]) : (i8) -> i16
// CHECK:      %[[TT:.*]] = "llvm.trunc"(%[[TZ]]) : (i16) -> i8
// CHECK:      "func.return"(%[[TT]]) : (i8) -> ()

// select_to_iminmax_ugt, i64: rewritten to the umax intrinsic.
// CHECK:      ^{{.*}}(%[[IX:.*]] : i64, %[[IY:.*]] : i64):
// CHECK:      %[[IR:.*]] = "llvm.intr.umax"(%[[IX]], %[[IY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[IR]]) : (i64) -> ()

// select_to_iminmax_ugt, i8: the select survives.
// CHECK:      ^{{.*}}(%[[JX:.*]] : i8, %[[JY:.*]] : i8):
// CHECK:      %[[JR:.*]] = "llvm.select"(%{{.*}}, %[[JX]], %[[JY]]) : (i1, i8, i8) -> i8
// CHECK:      "func.return"(%[[JR]]) : (i8) -> ()
