module

public import Veir.Data.LLVM.Int.Bitblast

namespace Veir.Data.LLVM

public section

/--
The `Byte` type can have any bitwidth `w`. It carries a two's complement integer
value of width `w` and a per-bit poison mask modeling bitwise delayed undefined
behavior.
-/
structure Byte (w : Nat) where
  /-- A two's complement integer value of width `w`. -/
  val : BitVec w
  /-- A per-bit poison mask of width `w`. -/
  poison : BitVec w
  /-- Invariant: if a bit is poison, the corresponding bit in `val` is zero. -/
  h : val &&& poison = 0
deriving DecidableEq

namespace Byte

@[veir_bv_normalize]
def cast {w₁ w₂ : Nat} (x : Byte w₁) (h : w₁ = w₂) : Byte w₂ :=
  ⟨x.val.cast h, x.poison.cast h, by simp [x.h]⟩

@[simp, grind =]
theorem cast_self {w : Nat} (x : Byte w) (h : w = w) : cast x h = x := by
  simp [cast]

@[veir_bv_normalize]
def allPoison : Byte w :=
  ⟨0, BitVec.allOnes w, by simp⟩

def and (x y : Byte w) : Byte w :=
  let poison := x.poison ||| y.poison
  ⟨(x.val &&& y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩

instance {w : Nat} : AndOp (Byte w) := ⟨and⟩

def or (x y : Byte w) : Byte w :=
  let poison := x.poison ||| y.poison
  ⟨(x.val ||| y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩

instance {w : Nat} : OrOp (Byte w) := ⟨or⟩

def xor (x y : Byte w) : Byte w :=
  let poison := x.poison ||| y.poison
  ⟨(x.val ^^^ y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩

instance {w : Nat} : XorOp (Byte w) := ⟨xor⟩

@[veir_bv_normalize]
def trunc (x : Byte w) (w' : Nat) : Byte w' :=
  ⟨x.val.truncate w', x.poison.truncate w', by (
    simp [←BitVec.setWidth_and, x.h]
  )⟩

def shl {w : Nat} (x : Byte w) (y : Int w) (nuw : Bool := false) : Byte w := Id.run do
  let .val y' := y | allPoison

  if y' ≥ w then
    return allPoison

  if nuw ∧ (x.val <<< y') >>> y' ≠ x.val then
    return allPoison

  if nuw ∧ (x.poison <<< y') >>> y' ≠ x.poison then
    return allPoison

  ⟨x.val <<< y', x.poison <<< y', by simp [←BitVec.shiftLeft_and_distrib, x.h]⟩

@[veir_bv_normalize]
def lshr (x : Byte w) (y : Int w) (exact := false) : Byte w :=
  let y' := y.getValueD
  if y.isPoison || y' ≥ w then
    allPoison
  else if exact ∧ (x.val >>> y') <<< y' ≠ x.val then
    allPoison
  else if exact ∧ (x.poison >>> y') <<< y' ≠ x.poison then
    allPoison
  else
    ⟨x.val >>> y', x.poison >>> y', by (
      simp [←BitVec.ushiftRight_and_distrib, x.h]
    )⟩

def freeze (x : Byte w) : Byte w :=
  ⟨x.val, 0#w, by grind⟩

def toString_rec {w : Nat} (b : Byte w) : String :=
  if w = 0 then "" else
  s!"{if b.poison.getMsbD 0 then "?" else ToString.toString (b.val.getMsbD 0).toNat}{(b.trunc (w - 1)).toString_rec}"

instance {w : Nat} : ToString (Byte w) where
  toString (b : Byte w) := s!"0b{b.toString_rec}#{w}"

open LLVM.Int

/-- Convert from `Byte` and `Int`.
  A byte where no bit is poison is equal to an integer value.
  If any bit is poison, the integer type is also poison.
-/
def toInt {w : Nat} (x : Byte w) : Int w :=
  if x.poison = 0 then
    .val x.val
  else
    .poison

def fromInt {w : Nat} (x : Int w) : Byte w :=
  if h : x.isPoison then
    ⟨0, BitVec.allOnes w, by simp⟩
  else
    ⟨x.getValue, 0, by simp⟩

def toUInt64 (x : Byte 64) : UInt64 :=
  if x.poison = 0 then
    UInt64.ofBitVec x.val
  else
    0

@[simp, grind .]
def fromBitVec {w : Nat} (x : BitVec w) : Byte w :=
  ⟨x, 0, by simp⟩

@[simp, grind .]
def fromUInt64 (x : UInt64) : Byte 64 :=
  fromBitVec x.toBitVec

/--
  i is refined by i' if for each bit, either i is poison, or the bits are the same and i' is not poison.
-/
@[simp, grind ., veir_bv_normalize]
def isRefinedBy {w : Nat} (i i' : Veir.Data.LLVM.Byte w) : Prop :=
  (i.poison ||| ((i.val ^^^ ~~~i'.val) &&& ~~~i'.poison)) = BitVec.allOnes w

@[inherit_doc] infix:50 " ⊒ " => LLVM.Byte.isRefinedBy

@[simp, grind .]
theorem isRefinedBy_refl {w : Nat} (i : Byte w) : i ⊒ i := by
  grind

theorem isRefinedBy_trans {w : Nat} {i j k : Byte w}
    (h₁ : i ⊒ j) (h₂ : j ⊒ k) : i ⊒ k := by
  grind

/-- The all-poison byte is refined by any byte. -/
@[simp, grind .]
theorem allPoison_isRefinedBy {w : Nat} (b : Byte w) : (allPoison : Byte w) ⊒ b := by
  simp [allPoison]

/-! ## Greatest lower bound under refinement -/

/-- Per-bit form of a bit-vector equation. -/
private theorem getLsbD_congr {w : Nat} {a b : BitVec w} (h : a = b) (i : Nat) :
    a.getLsbD i = b.getLsbD i := congrArg (·.getLsbD i) h

/-- Two bytes are compatible if they agree on every bit both define. -/
@[expose] def Compatible {w : Nat} (x y : Byte w) : Prop :=
  (x.val ^^^ y.val) &&& ~~~x.poison &&& ~~~y.poison = 0

instance {w : Nat} (x y : Byte w) : Decidable (Compatible x y) :=
  inferInstanceAs (Decidable (_ = _))

/-- `merge` keeps the byte invariant: a poisoned bit has value 0. -/
theorem merge_and_eq_zero {w : Nat} (x y : Byte w) :
    (x.val ||| y.val) &&& (x.poison &&& y.poison) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hx := getLsbD_congr x.h i; have hy := getLsbD_congr y.h i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at *
  generalize x.val.getLsbD i = a at *; generalize x.poison.getLsbD i = b at *
  generalize y.val.getLsbD i = c at *; generalize y.poison.getLsbD i = d at *
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/--
Building block of `glb?`: poison only where both bytes are poison, elsewhere the defined value.
It is the greatest lower bound only for compatible bytes; use `glb?`.
-/
@[expose] def merge {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val ||| y.val, x.poison &&& y.poison, merge_and_eq_zero x y⟩

/-- For compatible bytes, `merge x y` refines `x`: it only fills in poisoned bits of `x`. -/
private theorem isRefinedBy_merge_left {w : Nat} (x y : Byte w) (h : Compatible x y) :
    x ⊒ merge x y := by
  simp only [isRefinedBy, merge, Compatible] at *
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 := getLsbD_congr h i; have hx := getLsbD_congr x.h i; have hy := getLsbD_congr y.h i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, hi, decide_true] at *
  generalize x.val.getLsbD i = a at *; generalize x.poison.getLsbD i = b at *
  generalize y.val.getLsbD i = c at *; generalize y.poison.getLsbD i = d at *
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- For compatible bytes, `merge x y` refines `y`. -/
private theorem isRefinedBy_merge_right {w : Nat} (x y : Byte w) (h : Compatible x y) :
    y ⊒ merge x y := by
  simp only [isRefinedBy, merge, Compatible] at *
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 := getLsbD_congr h i; have hx := getLsbD_congr x.h i; have hy := getLsbD_congr y.h i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, hi, decide_true] at *
  generalize x.val.getLsbD i = a at *; generalize x.poison.getLsbD i = b at *
  generalize y.val.getLsbD i = c at *; generalize y.poison.getLsbD i = d at *
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- Two bytes with a common refinement are compatible: they cannot disagree on a defined bit. -/
private theorem compatible_of_isRefinedBy {w : Nat} {x y e : Byte w} (hx : x ⊒ e) (hy : y ⊒ e) :
    Compatible x y := by
  simp only [isRefinedBy, Compatible] at *
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 := getLsbD_congr hx i; have h2 := getLsbD_congr hy i; have he := getLsbD_congr e.h i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, hi, decide_true] at *
  generalize x.val.getLsbD i = a at *; generalize x.poison.getLsbD i = b at *
  generalize y.val.getLsbD i = c at *; generalize y.poison.getLsbD i = d at *
  generalize e.val.getLsbD i = f at *; generalize e.poison.getLsbD i = g at *
  cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> cases g <;> simp_all

/-- Every common refinement of `x` and `y` refines `merge x y`. -/
private theorem merge_isRefinedBy {w : Nat} {x y e : Byte w} (hx : x ⊒ e) (hy : y ⊒ e) :
    merge x y ⊒ e := by
  simp only [isRefinedBy, merge] at *
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 := getLsbD_congr hx i; have h2 := getLsbD_congr hy i; have he := getLsbD_congr e.h i
  have hx' := getLsbD_congr x.h i; have hy' := getLsbD_congr y.h i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    BitVec.getLsbD_allOnes, hi, decide_true] at *
  generalize x.val.getLsbD i = a at *; generalize x.poison.getLsbD i = b at *
  generalize y.val.getLsbD i = c at *; generalize y.poison.getLsbD i = d at *
  generalize e.val.getLsbD i = f at *; generalize e.poison.getLsbD i = g at *
  cases a <;> cases b <;> cases c <;> cases d <;> cases f <;> cases g <;> simp_all

/-- Two bytes that refine each other are equal. -/
theorem isRefinedBy_antisymm {w : Nat} {x y : Byte w} (h₁ : x ⊒ y) (h₂ : y ⊒ x) :
    x = y := by
  have hx := x.h; have hy := y.h
  obtain ⟨xv, xp, _⟩ := x; obtain ⟨yv, yp, _⟩ := y
  simp only [isRefinedBy, Byte.mk.injEq] at *
  constructor
  all_goals
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have a1 := getLsbD_congr h₁ i; have a2 := getLsbD_congr h₂ i
    have a3 := getLsbD_congr hx i; have a4 := getLsbD_congr hy i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
      BitVec.getLsbD_allOnes, hi, decide_true] at *
    generalize xv.getLsbD i = a at *; generalize xp.getLsbD i = b at *
    generalize yv.getLsbD i = c at *; generalize yp.getLsbD i = d at *
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/--
The greatest lower bound of two bytes under refinement: the least defined byte both refine
to, or `none` if no byte refines both (some bit is defined in both with different values).
-/
@[expose] def glb? {w : Nat} (x y : Byte w) : Option (Byte w) :=
  if Compatible x y then some (merge x y) else none

/-- `glb?` is a lower bound: what it returns refines both bytes. -/
theorem glb?_isRefinedBy {w : Nat} {x y m : Byte w} (h : x.glb? y = some m) :
    x ⊒ m ∧ y ⊒ m := by
  unfold glb? at h
  split at h
  · next hc => cases h; exact ⟨isRefinedBy_merge_left x y hc, isRefinedBy_merge_right x y hc⟩
  · cases h

/--
`glb?` is the greatest lower bound: every byte that refines both refines what `glb?` returns.
-/
theorem glb?_greatest {w : Nat} {x y e : Byte w} (hx : x ⊒ e) (hy : y ⊒ e) :
    ∃ m, x.glb? y = some m ∧ m ⊒ e :=
  ⟨merge x y, by simp [glb?, compatible_of_isRefinedBy hx hy], merge_isRefinedBy hx hy⟩

/-- If `glb?` returns `none`, no byte refines both. -/
theorem glb?_eq_none {w : Nat} {x y : Byte w} (h : x.glb? y = none) :
    ¬ ∃ e, x ⊒ e ∧ y ⊒ e := by
  rintro ⟨e, hx, hy⟩
  obtain ⟨m, hm, _⟩ := glb?_greatest hx hy
  simp [hm] at h

end Byte

end
