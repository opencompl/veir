module

import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
public import Veir.Data.LLVM.Int.Basic
import Veir.ForLean
import Veir.Data.LLVM.Int.Simp

open Veir.Data.LLVM

namespace Veir.Data.LLVM.Int

/--
  We define a bitblastable structure `IntBv`, where the `toBitVec` fields contains a bitvector,
  the `poison` field indicates whether the value is poison,
  and `inv` preserves a proof that if the value is poison its corresponding bitvector
  value is `0#w`.
-/
@[ext]
structure IntBv (w : Nat) where
  toBitVec : BitVec w
  poison : Bool
deriving DecidableEq

-- /-- An `LLVM.Int w` is converted into a structure `IntBv`, where
--   the `poison` field indicates whether the `Int` is poison. -/
-- def toIntBv {w : Nat} (x : Int w) : IntBv w :=
--   match h : x with
--   | .val v => {toBitVec := v, poison := false}
--   | .poison => {toBitVec := 0#w, poison := true}

-- /-- Return a boolean if the LLVM.int `x` is poison. -/
-- def isPoison {w : Nat} (x : Int w) : Bool := x.toIntBv.poison

-- /-- Return a concrete bitvector value given an LLVM.Int. -/
-- def getValue {w : Nat} (x : Int w) : BitVec w := x.toIntBv.toBitVec

@[llvm_toBitVec]
def isRefinedBy_toBitVec (i i' : IntBv w) :=
  i.poison ∨ (¬i.poison ∧ ¬i'.poison ∧ (i.toBitVec = i'.toBitVec))

@[llvm_toBitVec]
def is_eqv_bv (i : Int w) (i_bv : IntBv w) :=
  match i with
  | val v => i_bv.poison = false ∧ i_bv.toBitVec = v
  | poison => i_bv.poison = true

-- /--
--   We prove the injectivity of `toIntBv`.
-- -/
-- theorem toIntBv.inj {w : Nat} {x y : Int w} (h : x.toIntBv = y.toIntBv) : x = y :=
--   match x, y with
--   | .val v,  .val v' => by
--     simp only [toIntBv, IntBv.mk.injEq, and_true] at h
--     simp [h]
--   | .poison, .poison => rfl
--   | .val v,  .poison => by
--     simp [toIntBv] at h
--   | .poison, .val v => by
--     simp [toIntBv] at h


-- @[llvm_toBitVec]
-- theorem int_inj {w : Nat} (i1 i2 : Int w) :
--     i1 = i2 ↔ i1.toIntBv = i2.toIntBv := ⟨(· ▸ rfl), by apply toIntBv.inj⟩

-- @[llvm_toBitVec]
-- theorem toIntBv_poison {w : Nat} :
--     poison.toIntBv = ⟨0#w, true, by simp⟩ := by
--   simp [toIntBv]

-- @[llvm_toBitVec]
-- theorem toIntBv_val {w : Nat} {v : BitVec w} :
--     (val v).toIntBv = ⟨v, false, by simp⟩ := by
--   simp [toIntBv]

-- @[llvm_toBitVec]
-- theorem getValue_of_val {w : Nat} {v : BitVec w} :
--     (val v).getValue = v := rfl

-- @[llvm_toBitVec]
-- theorem getValue_of_poison {w : Nat} :
--     poison.getValue = 0#w := rfl

-- @[llvm_toBitVec]
-- theorem isPoison_of_val {w : Nat} {v : BitVec w} :
--     (val v).isPoison = false := rfl

-- @[llvm_toBitVec]
-- theorem isPoison_of_poison {w : Nat} :
--     poison.isPoison (w := w) = true := rfl

-- @[llvm_toBitVec]
-- theorem ite_eq_toIntBv {w : Nat} (x : Int w) :
--    (if x.isPoison then {toBitVec := 0#w, poison := true} else
--       {toBitVec := x.getValue, poison := false}) = x.toIntBv := by
--   rcases x <;> simp [llvm_toBitVec, isPoison]
--   <;> split <;> simp [toIntBv]

-- @[llvm_toBitVec]
-- theorem poison_ite_eq {w : Nat} (x y : Int w) (z : BitVec w) :
--   (if x.isPoison = true ∨ y.isPoison = true then
--       ({ toBitVec := 0#w, poison := true, inv := by simp} : IntBv w) else
--       ({ toBitVec := z, poison := false, inv := by simp} : IntBv w)).poison =
--       (x.isPoison ∨ y.isPoison) := by
  -- split
  -- · case _ h =>  simp [h]
  -- · case _ h => simpa using h

-- @[llvm_toBitVec]
-- theorem toIntBv_ite_eq {w : Nat} (x y : Int w) (c1 : Prop) [Decidable c1] :
--     (if c1 then x else y).toIntBv = if c1 then x.toIntBv else y.toIntBv:= by
--   rcases x <;> rcases y <;> simp [llvm_toBitVec]
--   <;> split <;> simp [toIntBv]

@[bv_normalize, llvm_toBitVec]
theorem isRefinedBy_toBitVec_eq (x y : Int w) :
    (x ⊑ y) ↔
      ∃ (x' : IntBv w) (h : is_eqv_bv x x'),
      ∃ (y' : IntBv w) (h : is_eqv_bv y y'),
        isRefinedBy_toBitVec x' y' := by
  simp [isRefinedBy, isRefinedBy_toBitVec]
  rcases x <;> rcases y
  · case _ v v' =>
    simp [llvm_toBitVec]
    constructor
    · intro heq
      let z : IntBv w := {toBitVec := v, poison := false}
      let z' : IntBv w := {toBitVec := v', poison := false}
      exists z
      and_intros
      <;> simp [z]
      exists z'
    · intro hexists
      obtain ⟨z, hz, z', hz'⟩ := hexists
      simp [hz] at hz'
      simp [← hz, ← hz']
  · simp [llvm_toBitVec]
    grind
  · case _ v =>
    simp [llvm_toBitVec]
    intros
    let z : IntBv w := {toBitVec := 0#w, poison := true}
    let z' : IntBv w := {toBitVec := v, poison := false}
    exists z
    simp [z]
    exists z'
  · simp [llvm_toBitVec]
    let z : IntBv w := {toBitVec := 0#w, poison := true}
    exists z
    simp [z]
    exists z


@[bv_normalize]
theorem eq_iff {w : Nat} {x y : IntBv w} :
    x = y ↔ x.toBitVec = y.toBitVec ∧ x.poison = y.poison :=
  IntBv.ext_iff

@[bv_normalize, llvm_toBitVec]
theorem toBitVec_ite_eq {w : Nat} (b : Prop) [Decidable b] (x y : IntBv w) :
    (if b then x else y).toBitVec = if b then x.toBitVec else y.toBitVec := by
  split <;> rfl

@[bv_normalize, llvm_toBitVec]
theorem poison_ite {w : Nat} (b : Prop) [Decidable b] (x y : IntBv w) :
    (if b then x else y).poison = if b then x.poison else y.poison := by
  split <;> rfl

-- @[bv_normalize]
-- theorem poison_toBitVec_constraint {w : Nat} (x : IntBv w) :
--     x.poison = true → x.toBitVec = 0#w := x.inv

@[bv_normalize]
theorem toBitVec_bif {w : Nat} (b : Bool) (x y : IntBv w) :
    (bif b then x else y).toBitVec = bif b then x.toBitVec else y.toBitVec := by
  cases b <;> rfl

@[bv_normalize]
theorem poison_bif {w : Nat} (b : Bool) (x y : IntBv w) :
    (bif b then x else y).poison = bif b then x.poison else y.poison := by
  cases b <;> rfl

-- @[llvm_toBitVec, bv_normalize]
-- theorem getValue_eq_toBitVec_of_not_poison {w : Nat} {x : Int w} :
--     x.getValue = x.toIntBv.toBitVec := by rfl

-- @[bv_normalize]
-- theorem isPoison_eq_toIntBv_poison {w : Nat} (x : Int w) :
--     x.isPoison = x.toIntBv.poison := rfl

attribute [llvm_toBitVec] IntPred.eval

/-! # LLVM IR operations unfolding to `toIntBv` -/

@[llvm_toBitVec]
theorem val_is_eqv_bv (x : IntBv w) :
    (val v).is_eqv_bv x ↔ (x.poison = false ∧ x.toBitVec = v) := by
  simp [is_eqv_bv]

@[llvm_toBitVec]
theorem poison_is_eqv_bv (x : IntBv w) :
    poison.is_eqv_bv x ↔ x.poison := by
  simp [is_eqv_bv]

@[llvm_toBitVec]
theorem eq_of_val_is_eqv_bv (h : (val v).is_eqv_bv x):
    x.poison = false ∧ x.toBitVec = v := by
  simp [is_eqv_bv] at h
  simp [h]

@[llvm_toBitVec]
theorem poison_of_is_eqv_bv (x : IntBv w) (hx : poison.is_eqv_bv x) :
    x.poison = true := by
  simp [is_eqv_bv] at hx
  simp [hx]

@[llvm_toBitVec]
def bv_constant (w : Nat) (v : _root_.Int) : IntBv w := {toBitVec := BitVec.ofInt w v, poison := false}

@[llvm_toBitVec]
theorem constant_eq_bv :
  is_eqv_bv (constant w v) (bv_constant w v) := by
    simp [is_eqv_bv, constant, bv_constant]

@[llvm_toBitVec]
def bv_add (x y : IntBv w) : IntBv w :=
  {toBitVec := x.toBitVec + y.toBitVec, poison := x.poison ∨ y.poison}

@[llvm_toBitVec]
theorem add_eq_bv (x y : Int w) (x' y' : IntBv w) (hx : is_eqv_bv x x') (hy : is_eqv_bv y y') :
  is_eqv_bv (add x y) (bv_add x' y') := by
    simp [is_eqv_bv, add, bv_add]
    cases x <;> cases y
    · case _ v v' =>
      have hx' := eq_of_val_is_eqv_bv (v := v) hx
      have hy' := eq_of_val_is_eqv_bv (v := v') hy
      simp [llvm_toBitVec, Id.run, hx', hy']
    · have := poison_of_is_eqv_bv y' hy
      simp [llvm_toBitVec, Id.run, this]
    · have := poison_of_is_eqv_bv x' hx
      simp [llvm_toBitVec, Id.run, this]
    · have := poison_of_is_eqv_bv y' hy
      simp [llvm_toBitVec, Id.run, this]

@[llvm_toBitVec]
def bv_sub (x y : IntBv w) : IntBv w :=
  {toBitVec := x.toBitVec - y.toBitVec, poison := x.poison ∨ y.poison}

@[llvm_toBitVec]
theorem sub_eq_bv (x y : Int w) (x' y' : IntBv w) (hx : is_eqv_bv x x') (hy : is_eqv_bv y y') :
  is_eqv_bv (sub x y) (bv_sub x' y') := by
    simp [is_eqv_bv, sub, bv_sub]
    cases x <;> cases y
    · case _ v v' =>
      have hx' := eq_of_val_is_eqv_bv (v := v) hx
      have hy' := eq_of_val_is_eqv_bv (v := v') hy
      simp [llvm_toBitVec, Id.run, hx', hy']
    · have := poison_of_is_eqv_bv y' hy
      simp [llvm_toBitVec, Id.run, this]
    · have := poison_of_is_eqv_bv x' hx
      simp [llvm_toBitVec, Id.run, this]
    · have := poison_of_is_eqv_bv y' hy
      simp [llvm_toBitVec, Id.run, this]

@[llvm_toBitVec]
def bv_mul (x y : IntBv w) : IntBv w :=
  {toBitVec := x.toBitVec - y.toBitVec, poison := x.poison ∨ y.poison}

@[llvm_toBitVec]
theorem mul_eq_bv (x y : Int w) (x' y' : IntBv w) (hx : is_eqv_bv x x') (hy : is_eqv_bv y y') :
  is_eqv_bv (sub x y) (bv_sub x' y') := by
    simp [is_eqv_bv, sub, bv_sub]
    cases x <;> cases y
    · case _ v v' =>
      have hx' := eq_of_val_is_eqv_bv (v := v) hx
      have hy' := eq_of_val_is_eqv_bv (v := v') hy
      simp [llvm_toBitVec, Id.run, hx', hy']
    · have := poison_of_is_eqv_bv y' hy
      simp [llvm_toBitVec, Id.run, this]
    · have := poison_of_is_eqv_bv x' hx
      simp [llvm_toBitVec, Id.run, this]
    · have := poison_of_is_eqv_bv y' hy
      simp [llvm_toBitVec, Id.run, this]

end Int
