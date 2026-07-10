// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A combine may drop a poison-producing flag from an op it rewrites, but it must not
// transplant one onto an op it creates whose poison condition differs. These combines
// therefore clear the offending flag on the created op. The corresponding refinement
// lemmas, with counterexamples for the flags being cleared, live in
// `Veir/Passes/RISCVCombines/LLVMProofs.lean`.
//
// `overflowFlags` is a bitmask: 1 = nsw, 2 = nuw, 3 = both.

"builtin.module"() ({
  // AndShlShl: the created `shl` clears `nsw` but keeps `nuw`. The bits `X & Y` shifts
  // out are a subset of `Y`'s (so `nuw` survives), but `X & Y` can have a sign-changing
  // bit pattern where `Y` does not (so `nsw` cannot).
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %sx = "llvm.shl"(%x, %z) : (i64, i64) -> i64
    %sy = "llvm.shl"(%y, %z) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    %r = "llvm.and"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // AndTruncTrunc: the created `trunc` clears `nsw` but keeps `nuw`, for the same reason.
  "func.func"() <{function_type = (i64, i64) -> i32}> ({
  ^bb0(%x: i64, %y: i64):
    %tx = "llvm.trunc"(%x) : (i64) -> i32
    %ty = "llvm.trunc"(%y) <{"overflowFlags" = 3 : i32}> : (i64) -> i32
    %r = "llvm.and"(%tx, %ty) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // OrShlShl: the created `shl` clears both flags and the created `or` clears `disjoint`.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %sx = "llvm.shl"(%x, %z) : (i64, i64) -> i64
    %sy = "llvm.shl"(%y, %z) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    %r = "llvm.or"(%sx, %sy) <{disjoint}> : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // XorAshrAshr: the created `ashr` clears `exact`.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %sx = "llvm.ashr"(%x, %z) : (i64, i64) -> i64
    %sy = "llvm.ashr"(%y, %z) <{exact}> : (i64, i64) -> i64
    %r = "llvm.xor"(%sx, %sy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // OrZextZext: the created `zext` clears `nneg`.
  "func.func"() <{function_type = (i32, i32) -> i64}> ({
  ^bb0(%x: i32, %y: i32):
    %zx = "llvm.zext"(%x) : (i32) -> i64
    %zy = "llvm.zext"(%y) <{nneg}> : (i32) -> i64
    %r = "llvm.or"(%zx, %zy) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // OrAndAnd: the created `or` clears `disjoint`.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64, %z: i64):
    %ax = "llvm.and"(%x, %z) : (i64, i64) -> i64
    %ay = "llvm.and"(%y, %z) : (i64, i64) -> i64
    %r = "llvm.or"(%ax, %ay) <{disjoint}> : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // sub_add_reg_x_sub_y_add_x: the created `sub` clears the matched `sub`'s flags.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %a = "llvm.add"(%y, %x) : (i64, i64) -> i64
    %r = "llvm.sub"(%x, %a) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // sub_one_from_sub_rw: the created `add` clears the matched `sub`'s flags.
  "func.func"() <{function_type = (i64, i64) -> i64}> ({
  ^bb0(%x: i64, %y: i64):
    %d = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    %c1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %r = "llvm.sub"(%d, %c1) <{"overflowFlags" = 2 : i32}> : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // add_shift: the created `shl` and `sub` both clear their flags.
  "func.func"() <{function_type = (i64, i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64, %c: i64):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %negb = "llvm.sub"(%zero, %b) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    %s = "llvm.shl"(%negb, %c) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    %r = "llvm.add"(%a, %s) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// AndShlShl: nsw cleared, nuw (2) retained.
// CHECK:      ^{{.*}}(%[[X:.*]] : i64, %[[Y:.*]] : i64, %[[Z:.*]] : i64):
// CHECK:      %[[A:.*]] = "llvm.and"(%[[X]], %[[Y]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[S:.*]] = "llvm.shl"(%[[A]], %[[Z]]) <{"overflowFlags" = 2 : i32}> : (i64, i64) -> i64
// CHECK:      "func.return"(%[[S]]) : (i64) -> ()

// AndTruncTrunc: nsw cleared, nuw (2) retained.
// CHECK:      ^{{.*}}(%[[TX:.*]] : i64, %[[TY:.*]] : i64):
// CHECK:      %[[TA:.*]] = "llvm.and"(%[[TX]], %[[TY]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[TT:.*]] = "llvm.trunc"(%[[TA]]) <{"overflowFlags" = 2 : i32}> : (i64) -> i32
// CHECK:      "func.return"(%[[TT]]) : (i32) -> ()

// OrShlShl: both flags cleared on the shl, disjoint cleared on the or.
// CHECK:      ^{{.*}}(%[[OX:.*]] : i64, %[[OY:.*]] : i64, %[[OZ:.*]] : i64):
// CHECK:      %[[OO:.*]] = "llvm.or"(%[[OX]], %[[OY]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[OS:.*]] = "llvm.shl"(%[[OO]], %[[OZ]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[OS]]) : (i64) -> ()

// XorAshrAshr: exact cleared.
// CHECK:      ^{{.*}}(%[[AX:.*]] : i64, %[[AY:.*]] : i64, %[[AZ:.*]] : i64):
// CHECK:      %[[AXO:.*]] = "llvm.xor"(%[[AX]], %[[AY]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[AS:.*]] = "llvm.ashr"(%[[AXO]], %[[AZ]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[AS]]) : (i64) -> ()

// OrZextZext: nneg cleared.
// CHECK:      ^{{.*}}(%[[ZX:.*]] : i32, %[[ZY:.*]] : i32):
// CHECK:      %[[ZO:.*]] = "llvm.or"(%[[ZX]], %[[ZY]]) : (i32, i32) -> i32
// CHECK-NEXT: %[[ZZ:.*]] = "llvm.zext"(%[[ZO]]) : (i32) -> i64
// CHECK:      "func.return"(%[[ZZ]]) : (i64) -> ()

// OrAndAnd: disjoint cleared.
// CHECK:      ^{{.*}}(%[[BX:.*]] : i64, %[[BY:.*]] : i64, %[[BZ:.*]] : i64):
// CHECK:      %[[BO:.*]] = "llvm.or"(%[[BX]], %[[BY]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[BA:.*]] = "llvm.and"(%[[BO]], %[[BZ]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[BA]]) : (i64) -> ()

// sub_add_reg_x_sub_y_add_x: created sub carries no flags.
// CHECK:      ^{{.*}}(%[[SX:.*]] : i64, %[[SY:.*]] : i64):
// CHECK:      %[[SC:.*]] = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
// CHECK-NEXT: %[[SR:.*]] = "llvm.sub"(%[[SC]], %[[SY]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[SR]]) : (i64) -> ()

// sub_one_from_sub_rw: created add carries no flags.
// CHECK:      ^{{.*}}(%[[DX:.*]] : i64, %[[DY:.*]] : i64):
// CHECK:      %[[DC:.*]] = "llvm.mlir.constant"() <{"value" = -1 : i64}> : () -> i64
// CHECK-NEXT: %[[DXO:.*]] = "llvm.xor"(%[[DY]], %[[DC]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[DR:.*]] = "llvm.add"(%[[DXO]], %[[DX]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[DR]]) : (i64) -> ()

// add_shift: created shl and sub both carry no flags.
// CHECK:      ^{{.*}}(%[[FA:.*]] : i64, %[[FB:.*]] : i64, %[[FC:.*]] : i64):
// CHECK:      %[[FS:.*]] = "llvm.shl"(%[[FB]], %[[FC]]) : (i64, i64) -> i64
// CHECK-NEXT: %[[FR:.*]] = "llvm.sub"(%[[FA]], %[[FS]]) : (i64, i64) -> i64
// CHECK:      "func.return"(%[[FR]]) : (i64) -> ()
