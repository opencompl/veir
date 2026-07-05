module

public import Veir.Data.LLVM.Int.Basic
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

@[veir_bv_normalize]
def lshr (x : Byte w) (y : Int w) : Byte w :=
  if y.isPoison || y.getValueD ≥ w then
    allPoison
  else
    let y := y.getValueD
    ⟨x.val >>> y, x.poison >>> y, by (
      simp [←BitVec.ushiftRight_and_distrib, x.h]
    )⟩

def toString_rec {w : Nat} (b : Byte w) : String :=
  if w = 0 then "" else
  s!"{if b.poison.getMsbD 0 then "?" else ToString.toString (b.val.getMsbD 0).toNat}{(b.trunc (w - 1)).toString_rec}"

instance {w : Nat} : ToString (Byte w) where
  toString (b : Byte w) := s!"0b{b.toString_rec}#{w}"

open Int

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

def fromUInt64 (x : UInt64) : Byte 64 :=
  ⟨x.toBitVec, 0, by simp⟩

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

end Byte

end
