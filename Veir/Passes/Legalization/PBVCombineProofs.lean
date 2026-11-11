module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Dialects.GMIR.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.GMIR.Semantics

/-!
# Bounded refinement statements of the gMIR combines

The refinements of the combines of `CombinerHelper` (`combinePatterns`, `selectPatterns`,
`redundant_and`, `redundant_and_select`, `sub_to_add` and `preLegalizerPatterns`), at every width up
to 8 bits, each by `veir_bv_normalize` and `pbv_decide 8`, for iterating on `pbv_decide` without the
Puddle validity proofs.

The first part restates the local correctness lemmas that the CTree validity proofs of
`luisa/legalization-proofs` use (`Validity/Combine.lean` and `Proofs.lean`), with a bound on each
width. The second states the combines that have no such lemma, read off their patterns.

Modelling conventions, as in `PBVProofs`:
* A matched `g_constant` is `.val c` for `c` of the type of its result, and the matcher's condition
  on its attribute is a condition on `c`: verified IR ties the two widths together.
* Flags of matched operations are arbitrary; created operations have no flags unless the pattern
  sets them.
* Shift amounts have the type of the shifted value.
* A `g_icmp` result wider than `i1` is the `i1` comparison zero-extended.
-/

public section

namespace Veir.Data.LLVM.PBVCombines

/-- The predicate of `icmp pred y x` that is equivalent to `icmp pred x y`, as in `CombinerHelper`. -/
def swapIntPred : LLVM.IntPred → LLVM.IntPred
  | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
  | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule
  | pred => pred

/-- The negation of a predicate, the `(pred, inverse)` pairs of `not_cmp_fold_pattern`. -/
def invertIntPred : LLVM.IntPred → LLVM.IntPred
  | .eq => .ne | .ne => .eq
  | .ugt => .ule | .uge => .ult | .ult => .uge | .ule => .ugt
  | .sgt => .sle | .sge => .slt | .slt => .sge | .sle => .sgt

/-- The `i1` negation that `createNot` builds. -/
def notI1 (c : LLVM.Int 1) : LLVM.Int 1 := LLVM.Int.xor c (LLVM.Int.constant 1 (-1))

/-- The quotient that `sdiv_by_pow2_pattern` builds for `sdiv x, 2^k`. -/
def sdivPow2Shift {w : Nat} (x : LLVM.Int w) (k : Nat) : LLVM.Int w :=
  LLVM.Int.ashr
    (LLVM.Int.add x
      (LLVM.Int.lshr (LLVM.Int.ashr x (LLVM.Int.constant w (w - 1 : Nat)))
        (LLVM.Int.constant w (w - k : Nat))))
    (LLVM.Int.constant w k)

/-! ## Combines with a local correctness lemma -/

theorem hoist_and_shl {w : Nat} (x y s : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.shl s n₁ u₁).and (y.shl s n₂ u₂) ⊒ (x.and y).shl s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_and_lshr {w : Nat} (x y s : LLVM.Int w) (e₁ e₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.lshr s e₁).and (y.lshr s e₂) ⊒ (x.and y).lshr s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_and_ashr {w : Nat} (x y s : LLVM.Int w) (e₁ e₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.ashr s e₁).and (y.ashr s e₂) ⊒ (x.and y).ashr s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_and_and {w : Nat} (x y z : LLVM.Int w)
    (bound_w : w ≤ 8) : (x.and z).and (y.and z) ⊒ (x.and y).and z := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_or_shl {w : Nat} (x y s : LLVM.Int w) (n₁ u₁ n₂ u₂ d : Bool)
    (bound_w : w ≤ 8) :
    (x.shl s n₁ u₁).or (y.shl s n₂ u₂) d ⊒ (x.or y).shl s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_or_lshr {w : Nat} (x y s : LLVM.Int w) (e₁ e₂ d : Bool)
    (bound_w : w ≤ 8) :
    (x.lshr s e₁).or (y.lshr s e₂) d ⊒ (x.or y).lshr s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_or_ashr {w : Nat} (x y s : LLVM.Int w) (e₁ e₂ d : Bool)
    (bound_w : w ≤ 8) :
    (x.ashr s e₁).or (y.ashr s e₂) d ⊒ (x.or y).ashr s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_or_and {w : Nat} (x y z : LLVM.Int w) (d : Bool)
    (bound_w : w ≤ 8) : (x.and z).or (y.and z) d ⊒ (x.or y).and z := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_xor_shl {w : Nat} (x y s : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.shl s n₁ u₁).xor (y.shl s n₂ u₂) ⊒ (x.xor y).shl s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_xor_lshr {w : Nat} (x y s : LLVM.Int w) (e₁ e₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.lshr s e₁).xor (y.lshr s e₂) ⊒ (x.xor y).lshr s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_xor_ashr {w : Nat} (x y s : LLVM.Int w) (e₁ e₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.ashr s e₁).xor (y.ashr s e₂) ⊒ (x.xor y).ashr s := by
  veir_bv_normalize
  pbv_decide 8

theorem hoist_xor_and {w : Nat} (x y z : LLVM.Int w)
    (bound_w : w ≤ 8) : (x.and z).xor (y.and z) ⊒ (x.xor y).and z := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_add_reg_x_add_y_sub_y {w : Nat} (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.add y n₁ u₁).sub y n₂ u₂ ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_add_reg_x_add_y_sub_x {w : Nat} (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    (x.add y n₁ u₁).sub x n₂ u₂ ⊒ y := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_add_reg_negate {w : Nat} (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    x.sub (y.add x n₁ u₁) n₂ u₂ ⊒ (LLVM.Int.val 0#w).sub y := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_add_reg_negate_x_first {w : Nat} (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    x.sub (x.add y n₁ u₁) n₂ u₂ ⊒ (LLVM.Int.val 0#w).sub y := by
  veir_bv_normalize
  pbv_decide 8

theorem xor_of_and_with_same_reg {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) :
    (x.and y).xor y ⊒ (x.xor (.val (BitVec.ofInt w (-1)))).and y := by
  veir_bv_normalize
  pbv_decide 8

theorem trunc_of_zext {w : Nat} {W : Nat} (x : LLVM.Int w) (h : w < W) (h' : W > w) (nneg nsw nuw : Bool)
    (bound_W : W ≤ 8) (bound_w : w ≤ 8) :
    (x.zext W nneg h).trunc w nsw nuw h' ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem trunc_of_sext {w : Nat} {W : Nat} (x : LLVM.Int w) (h : w < W) (h' : W > w) (nsw nuw : Bool)
    (bound_W : W ≤ 8) (bound_w : w ≤ 8) :
    (x.sext W h).trunc w nsw nuw h' ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem add_eq_self {w : Nat} (x y : LLVM.Int w) (n u : Bool)
    (bound_w : w ≤ 8) :
    (x.add y n u).icmp x .eq ⊒ y.icmp (.val 0#w) .eq := by
  veir_bv_normalize
  pbv_decide 8

theorem add_ne_self {w : Nat} (x y : LLVM.Int w) (n u : Bool)
    (bound_w : w ≤ 8) :
    (x.add y n u).icmp x .ne ⊒ y.icmp (.val 0#w) .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_eq_self {w : Nat} (x y : LLVM.Int w) (n u : Bool)
    (bound_w : w ≤ 8) :
    (x.sub y n u).icmp x .eq ⊒ y.icmp (.val 0#w) .eq := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_ne_self {w : Nat} (x y : LLVM.Int w) (n u : Bool)
    (bound_w : w ≤ 8) :
    (x.sub y n u).icmp x .ne ⊒ y.icmp (.val 0#w) .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem xor_eq_self {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : (x.xor y).icmp x .eq ⊒ y.icmp (.val 0#w) .eq := by
  veir_bv_normalize
  pbv_decide 8

theorem xor_ne_self {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : (x.xor y).icmp x .ne ⊒ y.icmp (.val 0#w) .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem combine_or_of_and_left {w : Nat} (x y : LLVM.Int w) (d : Bool)
    (bound_w : w ≤ 8) : (x.and y).or x d ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem combine_or_of_and_left' {w : Nat} (x y : LLVM.Int w) (d : Bool)
    (bound_w : w ≤ 8) : (y.and x).or x d ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem combine_or_of_and_right {w : Nat} (x y : LLVM.Int w) (d : Bool)
    (bound_w : w ≤ 8) : x.or (x.and y) d ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem combine_or_of_and_right' {w : Nat} (x y : LLVM.Int w) (d : Bool)
    (bound_w : w ≤ 8) : x.or (y.and x) d ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusBMinusC {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) :
    a.sub (b.sub c n₁ u₁) n₂ u₂ ⊒ a.add (c.sub b) := by
  veir_bv_normalize
  pbv_decide 8

theorem zext_of_zext {w : Nat} {M W : Nat} (x : LLVM.Int w) (h₁ : w < M) (h₂ : M < W) (h₃ : w < W)
    (n₁ n₂ : Bool)
    (bound_M : M ≤ 8) (bound_W : W ≤ 8) (bound_w : w ≤ 8) : (x.zext M n₁ h₁).zext W n₂ h₂ ⊒ x.zext W false h₃ := by
  veir_bv_normalize
  pbv_decide 8

theorem sext_of_sext {w : Nat} {M W : Nat} (x : LLVM.Int w) (h₁ : w < M) (h₂ : M < W) (h₃ : w < W)
    (bound_M : M ≤ 8) (bound_W : W ≤ 8) (bound_w : w ≤ 8) :
    (x.sext M h₁).sext W h₂ ⊒ x.sext W h₃ := by
  veir_bv_normalize
  pbv_decide 8

/-- `canonicalize_icmp_pattern`: swapping the operands of a comparison swaps its predicate. -/
theorem icmp_swap {w : Nat} (k x : Data.LLVM.Int w) (p : Data.LLVM.IntPred)
    (bound_w : w ≤ 8) :
    k.icmp x p ⊒ x.icmp k (swapIntPred p) := by
  veir_bv_normalize
  pbv_decide 8

theorem bitreverse_shl {w : Nat} (x s : LLVM.Int w) (n u : Bool)
    (bound_w : w ≤ 8) :
    (x.bitreverse.shl s n u).bitreverse ⊒ x.lshr s := by
  veir_bv_normalize
  pbv_decide 8

theorem bitreverse_lshr {w : Nat} (x s : LLVM.Int w) (e : Bool)
    (bound_w : w ≤ 8) :
    (x.bitreverse.lshr s e).bitreverse ⊒ x.shl s := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_same_val_and {w : Nat} (x : LLVM.Int w)
    (bound_w : w ≤ 8) : x.and x ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_same_val_or {w : Nat} (x : LLVM.Int w) (d : Bool)
    (bound_w : w ≤ 8) : x.or x d ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem same_val_zero_sub {w : Nat} (x : LLVM.Int w) (n u : Bool)
    (bound_w : w ≤ 8) : x.sub x n u ⊒ LLVM.Int.val 0#w := by
  veir_bv_normalize
  pbv_decide 8

theorem same_val_zero_xor {w : Nat} (x : LLVM.Int w)
    (bound_w : w ≤ 8) : x.xor x ⊒ LLVM.Int.val 0#w := by
  veir_bv_normalize
  pbv_decide 8

theorem add_sub_reg_0 {w : Nat} (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) : x.add (y.sub x n₁ u₁) n₂ u₂ ⊒ y := by
  veir_bv_normalize
  pbv_decide 8

theorem add_sub_reg_1 {w : Nat} (x y : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) : (y.sub x n₁ u₁).add x n₂ u₂ ⊒ y := by
  veir_bv_normalize
  pbv_decide 8

theorem APlusBMinusCMinusB {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool)
    (bound_w : w ≤ 8) :
    (a.add (b.sub c n₁ u₁) n₂ u₂).sub b n₃ u₃ ⊒ a.sub c := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusBMinusCMinusC {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool)
    (bound_w : w ≤ 8) :
    (a.sub (b.sub c n₁ u₁) n₂ u₂).sub c n₃ u₃ ⊒ a.sub b := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusBPlusCMinusA {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool)
    (bound_w : w ≤ 8) :
    (a.sub b n₁ u₁).add (c.sub a n₂ u₂) n₃ u₃ ⊒ c.sub b := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusBPlusBMinusC {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool)
    (bound_w : w ≤ 8) :
    (a.sub b n₁ u₁).add (b.sub c n₂ u₂) n₃ u₃ ⊒ a.sub c := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusBMinusA {w : Nat} (a b : LLVM.Int w) (n₁ u₁ n₂ u₂ : Bool)
    (bound_w : w ≤ 8) : a.sub (a.sub b n₁ u₁) n₂ u₂ ⊒ b := by
  veir_bv_normalize
  pbv_decide 8

theorem APlusBMinusAPlusC {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool)
    (bound_w : w ≤ 8) :
    a.add (b.sub (a.add c n₁ u₁) n₂ u₂) n₃ u₃ ⊒ b.sub c := by
  veir_bv_normalize
  pbv_decide 8

theorem APlusBMinusCPlusA {w : Nat} (a b c : LLVM.Int w) (n₁ u₁ n₂ u₂ n₃ u₃ : Bool)
    (bound_w : w ≤ 8) :
    a.add (b.sub (c.add a n₁ u₁) n₂ u₂) n₃ u₃ ⊒ b.sub c := by
  veir_bv_normalize
  pbv_decide 8

theorem select_same_val {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x : LLVM.Int w)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) : GMIR.selectNonzero c x x ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem select_ugt_umax {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .ugt) x y ⊒ x.umax y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_uge_umax {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .uge) x y ⊒ x.umax y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_sgt_smax {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .sgt) x y ⊒ x.smax y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_sge_smax {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .sge) x y ⊒ x.smax y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_ult_umin {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .ult) x y ⊒ x.umin y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_ule_umin {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .ule) x y ⊒ x.umin y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_slt_smin {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .slt) x y ⊒ x.smin y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_sle_smin {w : Nat} (x y : LLVM.Int w)
    (bound_w : w ≤ 8) : GMIR.selectNonzero (x.icmp y .sle) x y ⊒ x.smin y := by
  veir_bv_normalize
  pbv_decide 8

theorem zext_of_select {w : Nat} {wc W : Nat} (c : LLVM.Int wc) (x y : LLVM.Int w) (h : w < W) (nneg : Bool)
    (bound_wc : wc ≤ 8) (bound_W : W ≤ 8) (bound_w : w ≤ 8) :
    (GMIR.selectNonzero c x y).zext W nneg h ⊒
      GMIR.selectNonzero c (x.zext W false h) (y.zext W false h) := by
  veir_bv_normalize
  pbv_decide 8

theorem trunc_of_select {wc W : Nat} (c : LLVM.Int wc) (x y : LLVM.Int W) (h : W > w) (nsw nuw : Bool)
    (bound_wc : wc ≤ 8) (bound_W : W ≤ 8) :
    (GMIR.selectNonzero c x y).trunc w nsw nuw h ⊒
      GMIR.selectNonzero c (x.trunc w false false h) (y.trunc w false false h) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_sub' {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (x.sub k n u) x ⊒ x.sub (GMIR.selectNonzero c k (.val 0#w)) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_sub_swapped {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c x (x.sub k n u) ⊒ x.sub (GMIR.selectNonzero c (.val 0#w) k) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_add' {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (x.add k n u) x ⊒ x.add (GMIR.selectNonzero c k (.val 0#w)) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_add_swapped {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (n u : Bool)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c x (x.add k n u) ⊒ x.add (GMIR.selectNonzero c (.val 0#w) k) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_or' {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (d : Bool)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (x.or k d) x ⊒ x.or (GMIR.selectNonzero c k (.val 0#w)) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_or_swapped {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w) (d : Bool)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c x (x.or k d) ⊒ x.or (GMIR.selectNonzero c (.val 0#w) k) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_xor' {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (x.xor k) x ⊒ x.xor (GMIR.selectNonzero c k (.val 0#w)) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_xor_swapped {w : Nat} {wc : Nat} (c : LLVM.Int wc) (x k : LLVM.Int w)
    (bound_wc : wc ≤ 8) (bound_w : w ≤ 8) :
    GMIR.selectNonzero c x (x.xor k) ⊒ x.xor (GMIR.selectNonzero c (.val 0#w) k) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of `udiv_by_pow2_pattern`, whatever the `exact` flag. -/
theorem udiv_by_pow2 {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k < w) (exact : Bool)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    LLVM.Int.udiv x (LLVM.Int.val (BitVec.twoPow w k)) exact ⊒
      LLVM.Int.lshr x (LLVM.Int.constant w k) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` for a positive divisor. -/
theorem sdiv_exact_by_pow2_pos {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    LLVM.Int.sdiv x (LLVM.Int.val (BitVec.twoPow w k)) true ⊒
      LLVM.Int.ashr x (LLVM.Int.constant w k) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` for a negative divisor, including
    `-2^(w-1)`. -/
theorem sdiv_exact_by_pow2_neg {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k < w)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    LLVM.Int.sdiv x (LLVM.Int.val (-BitVec.twoPow w k)) true ⊒
      LLVM.Int.sub (LLVM.Int.constant w 0) (LLVM.Int.ashr x (LLVM.Int.constant w k)) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of `sdiv_by_pow2_pattern` for a positive divisor. -/
theorem sdiv_by_pow2_pos {w : Nat} (x : LLVM.Int w) (k : Nat) (hk0 : 0 < k) (hk : k + 1 < w)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    LLVM.Int.sdiv x (LLVM.Int.val (BitVec.twoPow w k)) ⊒ sdivPow2Shift x k := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of `sdiv_by_pow2_pattern` for a negative divisor, including
    `-2^(w-1)`. -/
theorem sdiv_by_pow2_neg {w : Nat} (x : LLVM.Int w) (k : Nat) (hk0 : 0 < k) (hk : k < w)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    LLVM.Int.sdiv x (LLVM.Int.val (-BitVec.twoPow w k)) ⊒
      LLVM.Int.sub (LLVM.Int.constant w 0) (sdivPow2Shift x k) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? 1 : 0` to `zext c`. -/
theorem select_one_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.constant w 1) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.zext c w false h := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? -1 : 0` to `sext c`. -/
theorem select_allOnes_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.constant w (-1)) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.sext c w h := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? 0 : 1` to `zext (not c)`. -/
theorem select_zero_one {w : Nat} (h : 1 < w) (c : LLVM.Int 1)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.constant w 1) ⊒
      LLVM.Int.zext (notI1 c) w false h := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? 0 : -1` to `sext (not c)`. -/
theorem select_zero_allOnes {w : Nat} (h : 1 < w) (c : LLVM.Int 1)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.constant w (-1)) ⊒
      LLVM.Int.sext (notI1 c) w h := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? F + 1 : F` to `add (zext c), F`. -/
theorem select_succ {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (f : BitVec w)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.val (f + 1)) (LLVM.Int.val f) ⊒
      LLVM.Int.add (LLVM.Int.zext c w false h) (LLVM.Int.val f) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? F - 1 : F` to `add (sext c), F`. -/
theorem select_pred {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (f : BitVec w)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.val (f - 1)) (LLVM.Int.val f) ⊒
      LLVM.Int.add (LLVM.Int.sext c w h) (LLVM.Int.val f) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? 2^k : 0` to `shl (zext c), k`. -/
theorem select_pow2_zero {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.val (BitVec.twoPow w k)) (LLVM.Int.constant w 0) ⊒
      LLVM.Int.shl (LLVM.Int.zext c w false h) (LLVM.Int.constant w k) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? 0 : 2^k` to `shl (zext (not c)), k`. -/
theorem select_zero_pow2 {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (k : Nat) (hk : k < w)
    (bound_w : w ≤ 8) (bound_k : k ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.constant w 0) (LLVM.Int.val (BitVec.twoPow w k)) ⊒
      LLVM.Int.shl (LLVM.Int.zext (notI1 c) w false h) (LLVM.Int.constant w k) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? -1 : F` to `or (sext c), F`. -/
theorem select_allOnes_const {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (f : BitVec w)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.constant w (-1)) (LLVM.Int.val f) ⊒
      LLVM.Int.or (LLVM.Int.sext c w h) (LLVM.Int.val f) := by
  veir_bv_normalize
  pbv_decide 8

/-- Prove the correctness of combining `c ? T : -1` to `or (sext (not c)), T`. -/
theorem select_const_allOnes {w : Nat} (h : 1 < w) (c : LLVM.Int 1) (t : BitVec w)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.val t) (LLVM.Int.constant w (-1)) ⊒
      LLVM.Int.or (LLVM.Int.sext (notI1 c) w h) (LLVM.Int.val t) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_shl {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (nsw nuw : Bool)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.shl x k nsw nuw) x ⊒
      LLVM.Int.shl x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_lshr {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (exact : Bool)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.lshr x k exact) x ⊒
      LLVM.Int.lshr x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_ashr {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w)
    (exact : Bool)
    (bound_w : w ≤ 8) :
    GMIR.selectNonzero c (LLVM.Int.ashr x k exact) x ⊒
      LLVM.Int.ashr x (GMIR.selectNonzero c k (LLVM.Int.constant w 0)) := by
  veir_bv_normalize
  pbv_decide 8

/--
Prove the correctness of combining `g_and (g_icmp p x y), 1` to `g_icmp p x y`, at every width: a
`g_icmp` wider than `i1` is its `i1` comparison zero-extended.
-/
theorem and_icmp_one (m : Nat) (h : 1 < m) (c : LLVM.Int 1)
    (bound_m : m ≤ 8) :
    LLVM.Int.zext c m false h ⊒
      LLVM.Int.and (LLVM.Int.zext c m false h) (LLVM.Int.constant m 1) := by
  veir_bv_normalize
  pbv_decide 8

/--
Prove all four `redundant_and_select_pattern` arm combinations at every width, for any mask with
its low bit set. The hypotheses admit poison from a comparison, including on an unselected arm;
`zext_i1_eq_poison_or_zero_or_one` supplies them for widened comparisons.
-/
theorem and_select_bool {w wc : Nat} (c : LLVM.Int wc) (t f : LLVM.Int w)
    (mask : BitVec w) (hmask : mask.toNat % 2 = 1)
    (ht : t = .poison ∨ t = .val 0#w ∨ t = .val 1#w)
    (hf : f = .poison ∨ f = .val 0#w ∨ f = .val 1#w)
    (bound_w : w ≤ 8) (bound_wc : wc ≤ 8) :
    LLVM.Int.and (GMIR.selectNonzero c t f) (.val mask) = GMIR.selectNonzero c t f := by
  veir_bv_normalize
  pbv_decide 8

/-- `redundant_and_pattern`, for an `i1` result: masking a comparison with an odd constant keeps it. -/
theorem and_icmp_odd {v : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1)
    (bound_v : v ≤ 8) : (x.icmp y p).and (.val (BitVec.ofInt 1 c)) ⊒ x.icmp y p := by
  veir_bv_normalize
  pbv_decide 8

/-- `redundant_and_pattern`, for a wider result: the comparison is zero-extended to `0` or `1`. -/
theorem and_zext_icmp_odd {v W : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) (hW : 1 < W)
    (bound_v : v ≤ 8) (bound_W : W ≤ 8) :
    ((x.icmp y p).zext W false hW).and (.val (BitVec.ofInt W c)) ⊒ (x.icmp y p).zext W false hW := by
  veir_bv_normalize
  pbv_decide 8

/-- `redundant_and_select_pattern .icmp .icmp`, for an `i1` result: both arms are comparisons. -/
theorem and_select_icmp_odd {wc v₁ v₂ : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1)
    (bound_wc : wc ≤ 8) (bound_v₁ : v₁ ≤ 8) (bound_v₂ : v₂ ≤ 8) :
    (GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q)).and (.val (BitVec.ofInt 1 k)) ⊒
      GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q) := by
  veir_bv_normalize
  pbv_decide 8

/-- `redundant_and_select_pattern .icmp .icmp`, for a wider result. -/
theorem and_select_zext_icmp_odd {wc v₁ v₂ W : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) (hW : 1 < W)
    (bound_wc : wc ≤ 8) (bound_v₁ : v₁ ≤ 8) (bound_v₂ : v₂ ≤ 8) (bound_W : W ≤ 8) :
    (GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW)).and
        (.val (BitVec.ofInt W k)) ⊒
      GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW) := by
  veir_bv_normalize
  pbv_decide 8

/-! ## Combines without a local correctness lemma -/

/-! ### `sub_to_add` -/

/-- `g_sub x, C` → `g_add x, -C`, dropping `nuw`, and `nsw` when `C` is the minimum signed value. -/
theorem sub_to_add {w : Nat} (x : LLVM.Int w) (c : BitVec w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.sub (.val c) nsw nuw ⊒ x.add (.val (-c)) (nsw && c != BitVec.intMin w) false := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `identity_combines` -/

theorem right_identity_zero_sub {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.sub (.val 0#w) nsw nuw ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem right_identity_zero_add {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.add (.val 0#w) nsw nuw ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem right_identity_zero_shl {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.shl (.val 0#w) nsw nuw ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem right_identity_zero_or {w : Nat} (x : LLVM.Int w) (disjoint : Bool) (bound : w ≤ 8) :
    x.or (.val 0#w) disjoint ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem right_identity_zero_xor {w : Nat} (x : LLVM.Int w) (bound : w ≤ 8) :
    x.xor (.val 0#w) ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem right_identity_zero_ashr {w : Nat} (x : LLVM.Int w) (exact : Bool) (bound : w ≤ 8) :
    x.ashr (.val 0#w) exact ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem right_identity_zero_lshr {w : Nat} (x : LLVM.Int w) (exact : Bool) (bound : w ≤ 8) :
    x.lshr (.val 0#w) exact ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

/-- `x * 1` → `x`; the constant `1` exists from width 1. -/
theorem right_identity_one_int {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (hw : 0 < w) (bound : w ≤ 8) :
    x.mul (.val 1#w) nsw nuw ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_right_to_zero {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.mul (.val 0#w) nsw nuw ⊒ (.val 0#w) := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_left_to_zero_shl {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    LLVM.Int.shl (.val 0#w) x nsw nuw ⊒ (.val 0#w) := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_left_to_zero_lshr {w : Nat} (x : LLVM.Int w) (exact : Bool) (bound : w ≤ 8) :
    LLVM.Int.lshr (.val 0#w) x exact ⊒ (.val 0#w) := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_left_to_zero_ashr {w : Nat} (x : LLVM.Int w) (exact : Bool) (bound : w ≤ 8) :
    LLVM.Int.ashr (.val 0#w) x exact ⊒ (.val 0#w) := by
  veir_bv_normalize
  pbv_decide 8

theorem binop_left_to_zero_mul {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    LLVM.Int.mul (.val 0#w) x nsw nuw ⊒ (.val 0#w) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Arithmetic with constants -/

theorem sub_minus_one {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val (BitVec.allOnes w)) x nsw nuw ⊒ x.xor (.val (BitVec.allOnes w)) := by
  veir_bv_normalize
  pbv_decide 8

theorem ZeroMinusAPlusB {w : Nat} (a b : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    (LLVM.Int.sub (.val 0#w) a n u).add b n' u' ⊒ b.sub a := by
  veir_bv_normalize
  pbv_decide 8

theorem APlusZeroMinusB {w : Nat} (a b : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    a.add (LLVM.Int.sub (.val 0#w) b n u) n' u' ⊒ a.sub b := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusZeroMinusB {w : Nat} (a b : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    a.sub (LLVM.Int.sub (.val 0#w) b n u) n' u' ⊒ a.add b := by
  veir_bv_normalize
  pbv_decide 8

/-- `(x - y) - 1` → `(y ^ -1) + x`; the matcher reads the constant as the signed `1`, so `1 < w`. -/
theorem sub_one_from_sub {w : Nat} (x y : LLVM.Int w) (n u n' u' : Bool) (hw : 1 < w) (bound : w ≤ 8) :
    (x.sub y n u).sub (.val 1#w) n' u' ⊒ (y.xor (LLVM.Int.constant w (-1))).add x := by
  veir_bv_normalize
  pbv_decide 8

theorem APlusC1MinusC2 {w : Nat} (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n u n' u' : Bool) (bound : w ≤ 8) :
    (a.add (.val c₁) n u).sub (.val c₂) n' u' ⊒ a.add (LLVM.Int.constant w (c₁.toInt - c₂.toInt)) := by
  veir_bv_normalize
  pbv_decide 8

theorem C2MinusAPlusC1 {w : Nat} (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n u n' u' : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val c₂) (a.add (.val c₁) n u) n' u' ⊒ (LLVM.Int.constant w (c₂.toInt - c₁.toInt)).sub a := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusC1MinusC2 {w : Nat} (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n u n' u' : Bool) (bound : w ≤ 8) :
    (a.sub (.val c₁) n u).sub (.val c₂) n' u' ⊒ a.sub (LLVM.Int.constant w (c₁.toInt + c₂.toInt)) := by
  veir_bv_normalize
  pbv_decide 8

theorem C1MinusAMinusC2 {w : Nat} (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n u n' u' : Bool) (bound : w ≤ 8) :
    (LLVM.Int.sub (.val c₁) a n u).sub (.val c₂) n' u' ⊒ (LLVM.Int.constant w (c₁.toInt - c₂.toInt)).sub a := by
  veir_bv_normalize
  pbv_decide 8

theorem AMinusC1PlusC2 {w : Nat} (a : LLVM.Int w) (c₁ c₂ : BitVec w) (n u n' u' : Bool) (bound : w ≤ 8) :
    (a.sub (.val c₁) n u).add (.val c₂) n' u' ⊒ a.add (LLVM.Int.constant w (c₂.toInt - c₁.toInt)) := by
  veir_bv_normalize
  pbv_decide 8

theorem sub_of_mul_const {w : Nat} (a x : LLVM.Int w) (c : BitVec w) (n u n' u' : Bool) (bound : w ≤ 8) :
    a.sub (x.mul (.val c) n u) n' u' ⊒ a.add (x.mul (LLVM.Int.constant w (-c.toInt))) := by
  veir_bv_normalize
  pbv_decide 8

theorem mul_by_neg_one {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.mul (.val (BitVec.allOnes w)) nsw nuw ⊒ (LLVM.Int.constant w 0).sub x nsw false := by
  veir_bv_normalize
  pbv_decide 8

/-- `x * 2` → `x + x`; the matcher reads the constant as the signed `2`, so `2 < w`. -/
theorem mulo_by_2 {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (hw : 2 < w) (bound : w ≤ 8) :
    x.mul (.val 2#w) nsw nuw ⊒ x.add x nsw nuw := by
  veir_bv_normalize
  pbv_decide 8

theorem add_shift {w : Nat} (a b c : LLVM.Int w) (n u n₁ u₁ n' u' : Bool) (bound : w ≤ 8) :
    a.add ((LLVM.Int.sub (.val 0#w) b n u).shl c n₁ u₁) n' u' ⊒ a.sub (b.shl c) := by
  veir_bv_normalize
  pbv_decide 8

theorem add_shift_swapped {w : Nat} (a b c : LLVM.Int w) (n u n₁ u₁ n' u' : Bool) (bound : w ≤ 8) :
    ((LLVM.Int.sub (.val 0#w) b n u).shl c n₁ u₁).add a n' u' ⊒ a.sub (b.shl c) := by
  veir_bv_normalize
  pbv_decide 8

theorem NotAPlusNegOne {w : Nat} (x : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    (x.add (.val (BitVec.allOnes w)) nsw nuw).xor (.val (BitVec.allOnes w)) ⊒ (LLVM.Int.constant w 0).sub x nsw nuw := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Logic with all ones -/

theorem or_and_xor_to_or {w : Nat} (x y : LLVM.Int w) (d : Bool) (bound : w ≤ 8) :
    (x.and (y.xor (.val (BitVec.allOnes w)))).or y d ⊒ x.or y := by
  veir_bv_normalize
  pbv_decide 8

theorem and_or_xor_to_and {w : Nat} (x y : LLVM.Int w) (d : Bool) (bound : w ≤ 8) :
    (x.or (y.xor (.val (BitVec.allOnes w))) d).and y ⊒ x.and y := by
  veir_bv_normalize
  pbv_decide 8

theorem or_and_xor_to_xor_or {w : Nat} (x y : LLVM.Int w) (d : Bool) (bound : w ≤ 8) :
    (x.and y).or (y.xor (.val (BitVec.allOnes w))) d ⊒ x.or (y.xor (.val (BitVec.allOnes w))) := by
  veir_bv_normalize
  pbv_decide 8

theorem and_or_xor_to_xor_and {w : Nat} (x y : LLVM.Int w) (d : Bool) (bound : w ≤ 8) :
    (x.or y d).and (y.xor (.val (BitVec.allOnes w))) ⊒ x.and (y.xor (.val (BitVec.allOnes w))) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `simplify_neg_minmax` -/

theorem simplify_neg_smax {w : Nat} (a : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val 0#w) (a.smax (LLVM.Int.sub (.val 0#w) a n u)) n' u' ⊒ a.smin (LLVM.Int.sub (.val 0#w) a n u) := by
  veir_bv_normalize
  pbv_decide 8

theorem simplify_neg_umax {w : Nat} (a : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val 0#w) (a.umax (LLVM.Int.sub (.val 0#w) a n u)) n' u' ⊒ a.umin (LLVM.Int.sub (.val 0#w) a n u) := by
  veir_bv_normalize
  pbv_decide 8

theorem simplify_neg_smin {w : Nat} (a : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val 0#w) (a.smin (LLVM.Int.sub (.val 0#w) a n u)) n' u' ⊒ a.smax (LLVM.Int.sub (.val 0#w) a n u) := by
  veir_bv_normalize
  pbv_decide 8

theorem simplify_neg_umin {w : Nat} (a : LLVM.Int w) (n u n' u' : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val 0#w) (a.umin (LLVM.Int.sub (.val 0#w) a n u)) n' u' ⊒ a.umax (LLVM.Int.sub (.val 0#w) a n u) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Comparisons

A `g_icmp` result wider than `i1` is the `i1` comparison zero-extended. -/

/-- `(icmp p x, y) ^ true` → `icmp (inverse p) x, y`. -/
theorem not_cmp_fold {v : Nat} (x y : LLVM.Int v) (p : LLVM.IntPred) (bound : v ≤ 8) :
    (x.icmp y p).xor (.val 1#1) ⊒ x.icmp y (invertIntPred p) := by
  veir_bv_normalize
  pbv_decide 8

theorem not_cmp_fold_wide {v W : Nat} (x y : LLVM.Int v) (p : LLVM.IntPred) (hW : 1 < W) (bound_v : v ≤ 8) (bound_W : W ≤ 8) :
    ((x.icmp y p).zext W false hW).xor (.val 1#W) ⊒ (x.icmp y (invertIntPred p)).zext W false hW := by
  veir_bv_normalize
  pbv_decide 8

theorem double_icmp_zero_and {v : Nat} (x y : LLVM.Int v) (d : Bool) (bound : v ≤ 8) :
    (x.icmp (.val 0#v) .eq).and (y.icmp (.val 0#v) .eq) ⊒ (x.or y).icmp (.val 0#v) .eq := by
  veir_bv_normalize
  pbv_decide 8

theorem double_icmp_zero_and_wide {v W : Nat} (x y : LLVM.Int v) (d : Bool) (hW : 1 < W) (bound_v : v ≤ 8) (bound_W : W ≤ 8) :
    ((x.icmp (.val 0#v) .eq).zext W false hW).and ((y.icmp (.val 0#v) .eq).zext W false hW) ⊒
      ((x.or y).icmp (.val 0#v) .eq).zext W false hW := by
  veir_bv_normalize
  pbv_decide 8

theorem double_icmp_zero_or {v : Nat} (x y : LLVM.Int v) (d : Bool) (bound : v ≤ 8) :
    (x.icmp (.val 0#v) .ne).or (y.icmp (.val 0#v) .ne) d ⊒ (x.or y).icmp (.val 0#v) .ne := by
  veir_bv_normalize
  pbv_decide 8

theorem double_icmp_zero_or_wide {v W : Nat} (x y : LLVM.Int v) (d : Bool) (hW : 1 < W) (bound_v : v ≤ 8) (bound_W : W ≤ 8) :
    ((x.icmp (.val 0#v) .ne).zext W false hW).or ((y.icmp (.val 0#v) .ne).zext W false hW) d ⊒
      ((x.or y).icmp (.val 0#v) .ne).zext W false hW := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Powers of two -/

/-- `x * 2^k` → `x << k`, for a constant that is a positive power of two as a signed integer. -/
theorem mul_to_shl {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w) (nsw nuw : Bool) (bound : w ≤ 8) :
    x.mul (.val (BitVec.twoPow w k)) nsw nuw ⊒ x.shl (LLVM.Int.constant w k) nsw nuw := by
  veir_bv_normalize
  pbv_decide 8

theorem urem_pow2_to_mask {w : Nat} (x : LLVM.Int w) (k : Nat) (hk : k + 1 < w) (bound : w ≤ 8) :
    x.urem (.val (BitVec.twoPow w k)) ⊒ x.and (LLVM.Int.constant w ((BitVec.twoPow w k).toInt - 1)) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### `constant_fold_binops`, with both constants read as signed integers -/

theorem constant_fold_add {w : Nat} (c₁ c₂ : BitVec w) (n u : Bool) (bound : w ≤ 8) :
    LLVM.Int.add (.val c₁) (.val c₂) n u ⊒ LLVM.Int.constant w (c₁.toInt + c₂.toInt) := by
  veir_bv_normalize
  pbv_decide 8

theorem constant_fold_sub {w : Nat} (c₁ c₂ : BitVec w) (n u : Bool) (bound : w ≤ 8) :
    LLVM.Int.sub (.val c₁) (.val c₂) n u ⊒ LLVM.Int.constant w (c₁.toInt - c₂.toInt) := by
  veir_bv_normalize
  pbv_decide 8

theorem constant_fold_mul {w : Nat} (c₁ c₂ : BitVec w) (n u : Bool) (bound : w ≤ 8) :
    LLVM.Int.mul (.val c₁) (.val c₂) n u ⊒ LLVM.Int.constant w (c₁.toInt * c₂.toInt) := by
  veir_bv_normalize
  pbv_decide 8

theorem constant_fold_smin {w : Nat} (c₁ c₂ : BitVec w) (bound : w ≤ 8) :
    LLVM.Int.smin (.val c₁) (.val c₂) ⊒ LLVM.Int.constant w (min c₁.toInt c₂.toInt) := by
  veir_bv_normalize
  pbv_decide 8

theorem constant_fold_smax {w : Nat} (c₁ c₂ : BitVec w) (bound : w ≤ 8) :
    LLVM.Int.smax (.val c₁) (.val c₂) ⊒ LLVM.Int.constant w (max c₁.toInt c₂.toInt) := by
  veir_bv_normalize
  pbv_decide 8

/-! ### Selects -/

theorem select_constant_cmp_nonzero {wc w : Nat} (c : BitVec wc) (x y : LLVM.Int w) (hc : c ≠ 0#wc) (bound_wc : wc ≤ 8) (bound : w ≤ 8) :
    GMIR.selectNonzero (.val c) x y ⊒ x := by
  veir_bv_normalize
  pbv_decide 8

theorem select_constant_cmp_zero {wc w : Nat} (x y : LLVM.Int w) (bound_wc : wc ≤ 8) (bound : w ≤ 8) :
    GMIR.selectNonzero (.val 0#wc) x y ⊒ y := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_shl_swapped {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w) (nsw nuw : Bool) (bound : w ≤ 8) :
    GMIR.selectNonzero c x (LLVM.Int.shl x k nsw nuw) ⊒
      LLVM.Int.shl x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_lshr_swapped {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w) (exact : Bool) (bound : w ≤ 8) :
    GMIR.selectNonzero c x (LLVM.Int.lshr x k exact) ⊒
      LLVM.Int.lshr x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) := by
  veir_bv_normalize
  pbv_decide 8

theorem select_into_ashr_swapped {w : Nat} (hw : 0 < w) (c : LLVM.Int 1) (x k : LLVM.Int w) (exact : Bool) (bound : w ≤ 8) :
    GMIR.selectNonzero c x (LLVM.Int.ashr x k exact) ⊒
      LLVM.Int.ashr x (GMIR.selectNonzero c (LLVM.Int.constant w 0) k) := by
  veir_bv_normalize
  pbv_decide 8

end Veir.Data.LLVM.PBVCombines

end
