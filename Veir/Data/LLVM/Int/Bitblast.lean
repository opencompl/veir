module

public meta import Veir.Meta.BVDecide
public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

public section

attribute [veir_bv_normalize] Bool.false_eq_true false_and or_self decide_false dite_eq_ite Bool.if_false_right
  Bool.decide_or Bool.decide_eq_true Bool.and_true Bool.or_eq_false_iff implies_true
  BitVec.truncate_eq_setWidth BitVec.setWidth_eq forall_const and_imp true_and
  BitVec.natCast_eq_ofNat ge_iff_le Bool.or_false dite_eq_ite Bool.if_true_left
  Bool.decide_or Bool.decide_eq_true Bool.or_eq_false_iff decide_eq_false_iff_not
  BitVec.not_le Nat.sub_zero and_imp dite_eq_ite Bool.if_true_left
  Bool.decide_or Bool.decide_eq_true Bool.or_eq_false_iff
  decide_eq_false_iff_not BitVec.not_le and_imp

attribute [veir_bv_normalize_post] dite_eq_ite Bool.if_true_left Bool.decide_or
  Bool.decide_eq_true Bool.or_eq_false_iff decide_eq_false_iff_not
  BitVec.not_le and_imp

/-- Return true if the LLVM.Int `x` is poison. -/
def isPoison {w : Nat} : (x : Int w) → Bool
  | .poison => true
  | .val _ => false

/-- Return the bitvector value of a non-poison `LLVM.Int`. -/
def getValue {w : Nat} (x : Int w) (h : x.isPoison = false := by grind) : BitVec w :=
  match x, h with
  | .val v, _ => v

/-- Return the bitvector value `v` of an `LLVM.Int` if it is not poison,
  or a zero bitvector `0#w` otherwise. -/
def getValueD {w : Nat} (x : Int w) : BitVec w :=
  match x with
  | .poison => 0#w
  | .val v => v

/-- The bitvector value of a non-poison `LLVM.Int` via `getValue` is equal to the default one,
  obtained by `getValueD`.
  This lemma should be applied when no more simplifications are available, such that `bv_decide` can
  reason about different instantiations of `getValue` without abstracting them separately.
-/
@[veir_bv_normalize_post]
theorem getValue_eq_getValueD {w : Nat} (x : Int w) (h : x.isPoison = false) :
    x.getValue h = x.getValueD := by
  simp [getValue, getValueD]
  cases x <;> grind

@[veir_bv_normalize]
theorem getValueD_eq (x : Int w) :
    x.getValueD = if h : x.isPoison = false then x.getValue h else 0 := by
  cases x <;> rfl

/-- Two elements `a b : LLVM.Int` are equal if and only if they return the same `isPoison` and,
  the same `getValue` in case they are *not* poison. -/
@[veir_bv_normalize]
theorem eq_iff {w : Nat} (a b : Int w) :
  a = b ↔
    (a.isPoison = b.isPoison) ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  simp [isPoison, getValue, veir_bv_normalize]
  grind

@[ext, grind ext]
theorem eq_ext {w : Nat} {a b : Int w} (hp : a.isPoison = b.isPoison) (hv : (a.getValueD = b.getValueD)) :
    a = b := by
  cases a <;> cases b
  · simp only [val.injEq]
    simp only [getValueD] at hv
    assumption
  · simp [isPoison] at hp
  · simp [isPoison] at hp
  · simp

/-- The value `getValue` of a `val v` is `v`. -/
@[simp, veir_bv_normalize, grind =]
theorem getValue_of_val {w : Nat} {v : BitVec w} :
    (val v).getValue (by grind [isPoison]) = v := by rfl

/-- An element `val v` is not poison. -/
@[simp, veir_bv_normalize, grind =]
theorem isPoison_of_val {w : Nat} {v : BitVec w} :
    (val v).isPoison = false := by rfl

/-- A `poison` element is poison. -/
@[simp, veir_bv_normalize, grind =]
theorem isPoison_of_poison {w : Nat} :
    poison.isPoison (w := w) = true := by rfl

@[simp, grind =]
theorem getValueD_val {w : Nat} {v : BitVec w} :
    (val v).getValueD = v := by rfl

@[simp, grind =]
theorem getValueD_poison {w : Nat} :
    poison.getValueD (w := w) = 0 := by rfl

/-- An element `b : LLVM.Int` refines an element `a : LLVM.Int` if either `a` is a poison value
  (in which case, any concrete or poison value refines it) or if `a` is not a poison value,
  `b` is not a poison value, and their concrete bitvector values are the same. -/
@[veir_bv_normalize, grind =]
theorem isRefinedBy_iff {w : Nat} (a b : Int w) :
  a ⊒ b ↔
    (a.isPoison = false → b.isPoison = false) ∧
    ((_ : a.isPoison = false) → (_ : b.isPoison = false) → a.getValue = b.getValue) := by
  simp [veir_bv_normalize, isPoison, getValue]
  grind [isRefinedBy]

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[veir_bv_normalize, grind =]
theorem getValue_constant {w : Nat} (v : _root_.Int) :
    (constant w v).getValue (by grind [constant]) = BitVec.ofInt w v := by rfl

@[veir_bv_normalize, grind =]
theorem isPoison_constant {w : Nat} (v : _root_.Int) :
    (constant w v).isPoison = false := by rfl

@[veir_bv_normalize, grind =]
theorem isPoison_poison {w : Nat} :
    (mlir_poison w).isPoison = true := by
  simp [mlir_poison, isPoison]

@[veir_bv_normalize, grind =]
theorem isPoison_add {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (add x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ BitVec.saddOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.uaddOverflow x.getValue y.getValue) := by
  simp only [isPoison, add, Id.run, getValue, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_add {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (add x y nsw nuw).isPoison = false) :
    (add x y nsw nuw).getValue h = x.getValue + y.getValue := by
  simp [add, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (sub x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ BitVec.ssubOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.usubOverflow x.getValue y.getValue) := by
  simp only [isPoison, sub, Id.run, getValue, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_sub {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (sub x y nsw nuw).isPoison = false) :
    (sub x y nsw nuw).getValue h = x.getValue - y.getValue := by
  simp [sub, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (mul x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ BitVec.smulOverflow x.getValue y.getValue) ∨
        (nuw ∧ BitVec.umulOverflow x.getValue y.getValue) := by
  simp only [mul, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_mul {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (mul x y nsw nuw).isPoison = false) :
    (mul x y nsw nuw).getValue h = x.getValue * y.getValue := by
  simp [mul, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_udiv {w : Nat} (x y : Int w) {exact : Bool} :
    (udiv x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (exact ∧ BitVec.umod x.getValue y.getValue ≠ 0) ∨
        (y.getValue = 0) := by
  simp only [udiv, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_udiv {w : Nat} (x y : Int w) {exact : Bool} (h : (udiv x y exact).isPoison = false) :
    (udiv x y exact).getValue h = x.getValue.udiv y.getValue := by
  simp [udiv, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_sdiv {w : Nat} (x y : Int w) {exact : Bool} :
    (sdiv x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (y.getValue = 0 ∨ (x.getValue = (BitVec.intMin w) ∧ y.getValue = -1)) ∨
        (exact ∧ BitVec.smod x.getValue y.getValue ≠ 0) ∨
        (y.getValue = 0) := by
  simp only [sdiv, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_sdiv {w : Nat} (x y : Int w) {exact : Bool} (h : (sdiv x y exact).isPoison = false) :
    (sdiv x y exact).getValue h = x.getValue.sdiv y.getValue := by
  simp [sdiv, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_urem {w : Nat} (x y : Int w) :
    (urem x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        y.getValue = 0 := by
  simp only [urem, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_urem {w : Nat} (x y : Int w) (h : (urem x y).isPoison = false) :
    (urem x y).getValue h = x.getValue.umod y.getValue := by
  simp [urem, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_srem {w : Nat} (x y : Int w) :
    (srem x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (y.getValue = 0 ∨ (x.getValue = (BitVec.intMin w) ∧ y.getValue = -1)) := by
  simp only [srem, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_srem {w : Nat} (x y : Int w) (h : (srem x y).isPoison = false) :
    (srem x y).getValue h = x.getValue.srem y.getValue := by
  simp [srem, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} :
    (shl x y nsw nuw).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        (nsw ∧ (x.getValue <<< y.getValue).sshiftRight' y.getValue ≠ x.getValue) ∨
        (nuw ∧ (x.getValue <<< y.getValue) >>> y.getValue ≠ x.getValue) ∨
        (y.getValue ≥ w) := by
  simp only [shl, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_shl {w : Nat} (x y : Int w) {nsw nuw : Bool} (h : (shl x y nsw nuw).isPoison = false) :
    (shl x y nsw nuw).getValue h = x.getValue <<< y.getValue := by
  simp only [shl, Id.run, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', ne_eq,
    BitVec.ushiftRight_eq', BitVec.natCast_eq_ofNat, ge_iff_le]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_lshr {w : Nat} (x y : Int w) {exact : Bool} :
    (lshr x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        y.getValue ≥ w ∨
        (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue) := by
  simp only [lshr, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_lshr {w : Nat} (x y : Int w) {exact : Bool} (h : (lshr x y exact).isPoison = false) :
    (lshr x y exact).getValue h = x.getValue >>> y.getValue := by
  simp only [lshr, Id.run, BitVec.natCast_eq_ofNat, ge_iff_le, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', ne_eq]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_ashr {w : Nat} (x y : Int w) {exact : Bool} :
    (ashr x y exact).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else
        y.getValue ≥ w ∨
        (exact ∧ (x.getValue >>> y.getValue) <<< y.getValue ≠ x.getValue) := by
  simp only [ashr, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_ashr {w : Nat} (x y : Int w) {exact : Bool} (h : (ashr x y exact).isPoison = false) :
    (ashr x y exact).getValue h = x.getValue.sshiftRight' y.getValue := by
  simp only [ashr, Id.run, BitVec.natCast_eq_ofNat, ge_iff_le, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', ne_eq, BitVec.sshiftRight_eq']
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_ctlz {w : Nat} (x : Int w) {is_zero_poison : Bool} :
    (ctlz x is_zero_poison).isPoison =
      if _ : x.isPoison = true then true else is_zero_poison && (x.getValue == 0#w) := by
  simp only [ctlz, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_ctlz {w : Nat} (x : Int w) {is_zero_poison : Bool}
    (h : (ctlz x is_zero_poison).isPoison = false) :
    (ctlz x is_zero_poison).getValue h = x.getValue.clz := by
  simp only [ctlz, isPoison, getValue, Id.run]
  simp [pure] at h ⊢
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_cttz {w : Nat} (x : Int w) {is_zero_poison : Bool} :
    (cttz x is_zero_poison).isPoison =
      if _ : x.isPoison = true then true else is_zero_poison && (x.getValue == 0#w) := by
  simp only [cttz, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_cttz {w : Nat} (x : Int w) {is_zero_poison : Bool}
    (h : (cttz x is_zero_poison).isPoison = false) :
    (cttz x is_zero_poison).getValue h = x.getValue.ctz := by
  simp only [cttz, isPoison, getValue, Id.run]
  simp [pure] at h ⊢
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_ctpop {w : Nat} (x : Int w) :
    (ctpop x).isPoison = x.isPoison := by
  simp [ctpop, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_ctpop {w : Nat} (x : Int w) (h : (ctpop x).isPoison = false) :
    (ctpop x).getValue h = x.getValue.cpop := by
  cases x <;> simp [ctpop, getValue, Id.run] at h ⊢

@[veir_bv_normalize, grind =]
theorem isPoison_bswap {w : Nat} (x : Int w) :
    (bswap x).isPoison = x.isPoison := by
  cases x with
  | poison => simp [bswap, isPoison, Id.run]
  | val x' =>
      by_cases h16 : w = 16
      · simp [bswap, isPoison, Id.run, pure, h16]
      · by_cases h32 : w = 32
        · simp [bswap, isPoison, Id.run, pure, h32]
        · by_cases h64 : w = 64
          · simp [bswap, isPoison, Id.run, pure, h64]
          · simp [bswap, isPoison, Id.run, h16, h32, h64]

@[veir_bv_normalize, grind =]
theorem getValue_bswap_32 (x : Int 32) (h : (bswap x).isPoison = false) :
    (bswap x).getValue h =
      x.getValue.extractLsb 7 0 ++ x.getValue.extractLsb 15 8 ++
      x.getValue.extractLsb 23 16 ++ x.getValue.extractLsb 31 24 := by
  cases x <;> simp [bswap, bswap32BV, getValue, Id.run, pure] at h ⊢

@[veir_bv_normalize, grind =]
theorem getValue_bswap_64 (x : Int 64) (h : (bswap x).isPoison = false) :
    (bswap x).getValue h =
      x.getValue.extractLsb 7 0 ++ x.getValue.extractLsb 15 8 ++
      x.getValue.extractLsb 23 16 ++ x.getValue.extractLsb 31 24 ++
      x.getValue.extractLsb 39 32 ++ x.getValue.extractLsb 47 40 ++
      x.getValue.extractLsb 55 48 ++ x.getValue.extractLsb 63 56 := by
  cases x <;> simp [bswap, bswap64BV, getValue, Id.run, pure] at h ⊢

@[veir_bv_normalize, grind =]
theorem isPoison_bitreverse {w : Nat} (x : Int w) :
    (bitreverse x).isPoison = x.isPoison := by
  cases x <;> simp [bitreverse, isPoison, Id.run]

@[veir_bv_normalize, grind =]
theorem getValue_bitreverse {w : Nat} (x : Int w) (h : (bitreverse x).isPoison = false) :
    (bitreverse x).getValue h = x.getValue.reverse := by
  cases x <;> simp [bitreverse, getValue, Id.run] at h ⊢

@[veir_bv_normalize, grind =]
theorem isPoison_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) :
    (cast x h).isPoison = x.isPoison := by
  simp [cast, isPoison]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) (hpoison : (cast x h).isPoison = false) :
    (cast x h).getValue hpoison = x.getValue.cast h := by
  simp [cast, getValue]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_and {w : Nat} (x y : Int w) :
    (and x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [and, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_and {w : Nat} (x y : Int w) (h : (and x y).isPoison = false) :
    (and x y).getValue h = x.getValue &&& y.getValue := by
  simp [and, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_or {w : Nat} (x y : Int w) {disjoint : Bool} :
    (or x y disjoint).isPoison =
      if h : x.isPoison ∨ y.isPoison then true
      else
        disjoint ∧ ((x.getValue &&& y.getValue) ≠ 0) := by
  simp only [or, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_or {w : Nat} (x y : Int w) {disjoint : Bool} (h : (or x y disjoint).isPoison = false) :
    (or x y disjoint).getValue h = x.getValue ||| y.getValue := by
  simp [or, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_xor {w : Nat} (x y : Int w) :
    (xor x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [xor, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_xor {w : Nat} (x y : Int w) (h : (xor x y).isPoison = false) :
    (xor x y).getValue h = x.getValue ^^^ y.getValue := by
  simp [xor, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) :
    (trunc x w₂ nsw nuw h).isPoison =
      if h : x.isPoison then true
      else
        (nsw ∧ (x.getValue.truncate w₂).signExtend w₁ ≠ x.getValue) ∨
        (nuw ∧ (x.getValue.truncate w₂).zeroExtend w₁ ≠ x.getValue) := by
  simp only [trunc, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_trunc {w₁ w₂: Nat} (x : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂) (hpoison : (trunc x w₂ nsw nuw h).isPoison = false) :
    (trunc x w₂ nsw nuw h).getValue hpoison = x.getValue.truncate w₂ := by
  simp [trunc, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_zext {w₁ w₂: Nat} (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) :
    (zext x w₂ nneg h).isPoison =
      if h : x.isPoison then true
      else
        nneg ∧ x.getValue.msb := by
  simp only [zext, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_zext (x : Int w₁) {nneg : Bool} (h : w₁ < w₂) (hpoison : (zext x w₂ nneg h).isPoison = false) :
    (zext x w₂ nneg h).getValue hpoison = x.getValue.zeroExtend w₂ := by
  simp [zext, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_sext {w₁ w₂: Nat} (x : Int w₁) (h : w₁ < w₂) :
    (sext x w₂ h).isPoison = x.isPoison := by
  simp [sext, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_sext {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ < w₂) (hpoison : (sext x w₂ h).isPoison = false) :
    (sext x w₂ h).getValue hpoison = x.getValue.signExtend w₂ := by
  simp [sext, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_icmp {w : Nat} (x y : Int w) (p : IntPred) :
    (icmp x y p).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [icmp, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_icmp {w : Nat} (x y : Int w) (p : IntPred) (h : (icmp x y p).isPoison = false) :
    (icmp x y p).getValue h = BitVec.ofBool (IntPred.eval p x.getValue y.getValue) := by
  simp [icmp, Id.run]
  grind

attribute [veir_bv_normalize, grind =] IntPred.eval

@[veir_bv_normalize, grind =]
theorem isPoison_select {w : Nat} (x y : Int w) (c : Int 1) :
    (select c x y).isPoison =
      if h : c.isPoison = true then true
      else if c.getValue = 1#1 then x.isPoison else y.isPoison := by
  simp [select, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_select {w : Nat} (x y : Int w) (c : Int 1) (h : (select c x y).isPoison = false) :
    (select c x y).getValue h = if _ : c.getValue = 1#1 then x.getValue else y.getValue := by
  simp [select, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_smax {w : Nat} (x y : Int w) :
    (smax x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [smax, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_smax {w : Nat} (x y : Int w) (h : (smax x y).isPoison = false) :
    (smax x y).getValue h = if x.getValue.sle y.getValue then y.getValue else x.getValue := by
  simp [smax, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_smin {w : Nat} (x y : Int w) :
    (smin x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [smin, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_smin {w : Nat} (x y : Int w) (h : (smin x y).isPoison = false) :
    (smin x y).getValue h = if x.getValue.sle y.getValue then x.getValue else y.getValue := by
  simp [smin, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_umax {w : Nat} (x y : Int w) :
    (umax x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [umax, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_umax {w : Nat} (x y : Int w) (h : (umax x y).isPoison = false) :
    (umax x y).getValue h = if x.getValue.ule y.getValue then y.getValue else x.getValue := by
  simp [umax, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_umin {w : Nat} (x y : Int w) :
    (umin x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp [umin, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_umin {w : Nat} (x y : Int w) (h : (umin x y).isPoison = false) :
    (umin x y).getValue h = if x.getValue.ule y.getValue then x.getValue else y.getValue := by
  simp [umin, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_saddSat {w : Nat} (x y : Int w) :
    (saddSat x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [saddSat, isPoison, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_saddSat {w : Nat} (x y : Int w) (h : (saddSat x y).isPoison = false) :
    (saddSat x y).getValue h =
      if BitVec.saddOverflow x.getValue y.getValue then
        (if x.getValue.msb then BitVec.intMin w else BitVec.intMax w)
      else x.getValue + y.getValue := by
  simp only [saddSat, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_uaddSat {w : Nat} (x y : Int w) :
    (uaddSat x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [uaddSat, isPoison, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_uaddSat {w : Nat} (x y : Int w) (h : (uaddSat x y).isPoison = false) :
    (uaddSat x y).getValue h =
      if BitVec.uaddOverflow x.getValue y.getValue then BitVec.allOnes w
      else x.getValue + y.getValue := by
  simp only [uaddSat, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_ssubSat {w : Nat} (x y : Int w) :
    (ssubSat x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [ssubSat, isPoison, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_ssubSat {w : Nat} (x y : Int w) (h : (ssubSat x y).isPoison = false) :
    (ssubSat x y).getValue h =
      if BitVec.ssubOverflow x.getValue y.getValue then
        (if x.getValue.msb then BitVec.intMin w else BitVec.intMax w)
      else x.getValue - y.getValue := by
  simp only [ssubSat, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_usubSat {w : Nat} (x y : Int w) :
    (usubSat x y).isPoison = decide (x.isPoison ∨ y.isPoison) := by
  simp only [usubSat, isPoison, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_usubSat {w : Nat} (x y : Int w) (h : (usubSat x y).isPoison = false) :
    (usubSat x y).getValue h =
      if BitVec.usubOverflow x.getValue y.getValue then BitVec.ofNat w 0
      else x.getValue - y.getValue := by
  simp only [usubSat, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_sshlSat {w : Nat} (x y : Int w) :
    (sshlSat x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else y.getValue ≥ w := by
  simp only [sshlSat, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_sshlSat {w : Nat} (x y : Int w) (h : (sshlSat x y).isPoison = false) :
    (sshlSat x y).getValue h =
      if (x.getValue <<< y.getValue).sshiftRight' y.getValue ≠ x.getValue then
        (if x.getValue.msb then BitVec.intMin w else BitVec.intMax w)
      else x.getValue <<< y.getValue := by
  simp only [sshlSat, Id.run, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', ne_eq,
    BitVec.natCast_eq_ofNat, ge_iff_le]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_ushlSat {w : Nat} (x y : Int w) :
    (ushlSat x y).isPoison =
      if h : x.isPoison = true ∨ y.isPoison = true then true
      else y.getValue ≥ w := by
  simp only [ushlSat, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_ushlSat {w : Nat} (x y : Int w) (h : (ushlSat x y).isPoison = false) :
    (ushlSat x y).getValue h =
      if (x.getValue <<< y.getValue) >>> y.getValue ≠ x.getValue then BitVec.allOnes w
      else x.getValue <<< y.getValue := by
  simp only [ushlSat, Id.run, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', ne_eq,
    BitVec.natCast_eq_ofNat, ge_iff_le]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_abs {w : Nat} (x : Int w) (is_int_min_poison : Bool) :
    (abs x is_int_min_poison).isPoison =
      if h : x.isPoison = true then true
      else is_int_min_poison ∧ x.getValue = BitVec.intMin w := by
  simp only [abs, isPoison, getValue, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_abs {w : Nat} (x : Int w) (is_int_min_poison : Bool)
    (h : (abs x is_int_min_poison).isPoison = false) :
    (abs x is_int_min_poison).getValue h =
      if x.getValue.msb then -x.getValue else x.getValue := by
  simp only [abs, Id.run]
  simp [pure]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_fshl {w : Nat} (a b c : Int w) :
    (fshl a b c).isPoison = decide (a.isPoison ∨ b.isPoison ∨ c.isPoison) := by
  simp [fshl, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_fshl {w : Nat} (a b c : Int w) (h : (fshl a b c).isPoison = false) :
    (fshl a b c).getValue h =
      ((a.getValue ++ b.getValue) <<< (c.getValue % BitVec.ofNat w w)).extractLsb' w w := by
  simp only [fshl, Id.run]
  rw [BitVec.shiftLeft_eq']
  simp [BitVec.toNat_umod]
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_fshr {w : Nat} (a b c : Int w) :
    (fshr a b c).isPoison = decide (a.isPoison ∨ b.isPoison ∨ c.isPoison) := by
  simp [fshr, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_fshr {w : Nat} (a b c : Int w) (h : (fshr a b c).isPoison = false) :
    (fshr a b c).getValue h =
      ((a.getValue ++ b.getValue) >>> (c.getValue % BitVec.ofNat w w)).truncate w := by
  simp only [fshr, Id.run]
  rw [BitVec.ushiftRight_eq']
  simp [BitVec.toNat_umod]
  grind

theorem add_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (nsw nuw : Bool) :
    add x₁ x₂ nsw nuw ⊒ add y₁ y₂ nsw nuw := by
  grind

theorem sub_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (nsw nuw : Bool) :
    sub x₁ x₂ nsw nuw ⊒ sub y₁ y₂ nsw nuw := by
  grind

theorem mul_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (nsw nuw : Bool) :
    mul x₁ x₂ nsw nuw ⊒ mul y₁ y₂ nsw nuw := by
  grind

theorem udiv_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (exact : Bool) :
    udiv x₁ x₂ exact ⊒ udiv y₁ y₂ exact := by
  grind

theorem sdiv_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (exact : Bool) :
    sdiv x₁ x₂ exact ⊒ sdiv y₁ y₂ exact := by
  grind

theorem urem_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) :
    urem x₁ x₂ ⊒ urem y₁ y₂ := by
  grind

theorem srem_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) :
    srem x₁ x₂ ⊒ srem y₁ y₂ := by
  grind

theorem shl_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (nsw nuw : Bool) :
    shl x₁ x₂ nsw nuw ⊒ shl y₁ y₂ nsw nuw := by
  grind

theorem lshr_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (exact : Bool) :
    lshr x₁ x₂ exact ⊒ lshr y₁ y₂ exact := by
  grind

theorem ashr_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (exact : Bool) :
    ashr x₁ x₂ exact ⊒ ashr y₁ y₂ exact := by
  grind

theorem cast_mono {w₁ w₂ : Nat} (x₁ x₂ : Int w₁) (h : w₁ = w₂)
    (h₁ : x₁ ⊒ x₂) :
    cast x₁ h ⊒ cast x₂ h := by
  grind

theorem and_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) :
    and x₁ x₂ ⊒ and y₁ y₂ := by
  grind

theorem or_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w) (disjoint : Bool)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) :
    or x₁ x₂ disjoint ⊒ or y₁ y₂ disjoint := by
  grind

theorem xor_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) :
    xor x₁ x₂ ⊒ xor y₁ y₂ := by
  grind

theorem trunc_mono {w₁ w₂ : Nat} (x₁ x₂ : Int w₁) {nsw nuw : Bool} (h : w₁ > w₂)
    (h₁ : x₁ ⊒ x₂) :
    trunc x₁ w₂ nsw nuw h ⊒ trunc x₂ w₂ nsw nuw h := by
  grind

theorem zext_mono {w₁ w₂ : Nat} (x₁ x₂ : Int w₁) {nneg : Bool} (h : w₁ < w₂)
    (h₁ : x₁ ⊒ x₂) :
    zext x₁ w₂ nneg h ⊒ zext x₂ w₂ nneg h := by
  grind

theorem sext_mono {w₁ w₂ : Nat} (x₁ x₂ : Int w₁) (h : w₁ < w₂)
    (h₁ : x₁ ⊒ x₂) :
    sext x₁ w₂ h ⊒ sext x₂ w₂ h := by
  grind

theorem icmp_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w) (p : IntPred)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) :
    icmp x₁ x₂ p ⊒ icmp y₁ y₂ p := by
  grind

theorem select_mono {w : Nat} (x₁ x₂ y₁ y₂ : Int w) (c₁ c₂ : Int 1)
    (h₁ : x₁ ⊒ y₁) (h₂ : x₂ ⊒ y₂) (h₃ : c₁ ⊒ c₂) :
    select c₁ x₁ x₂ ⊒ select c₂ y₁ y₂ := by
  grind

@[veir_bv_normalize, grind =]
theorem isPoison_freeze {w : Nat} (x : Int w) :
    (freeze x).isPoison = false := by
  simp [freeze, isPoison, Id.run]
  grind

@[veir_bv_normalize, grind =]
theorem getValue_freeze {w : Nat} (x : Int w) :
    (freeze x).getValue = if h : x.isPoison then 0#w else x.getValue := by
  simp [freeze, Id.run]
  grind
