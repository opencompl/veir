module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Interpreter.Memory

/-!
# Local lemmas for the byte, count and `alloca` translations

The local lemmas for the patterns of `llvm-to-gmir` that relate a byte to the integer of its bits,
or a count to its resized form. The patterns match the condition each lemma needs:

| Pattern | Lemma | Condition, and where it is checked |
|---|---|---|
| the counts | `resizeCount_self` | the result has the operand's type (`lowerCount`) |
| byte `trunc` | `byte_trunc_frozen` | no `nsw`/`nuw`, which the translation drops |
| byte/integer `bitcast` | `byte_toInt_frozen` | a nonzero width (`isByteIntBitcast`) |
| integer/byte round trip | `freezeByteWith_fromInt` | a nonzero width (`isIntToByteRoundTrip`) |
| byte `shl`, byte `lshr` | `byte_shl_frozen`, `byte_lshr_frozen` | the byte is not entirely poison |
| static `alloca` | `ptrFromInt_toInt` | the stack object has the size of the `alloca` |

The last two are not used: whether a byte is entirely poison is a property of the value, which no
matcher can check, and the static `alloca` computes the size of its stack object from the IR
(`MatchProg.inspectOperation`), which `Pattern.Valid` quantifies over.
-/

namespace Veir.LLVMToGMIR.CTreeProofs

open Data

/-- A count resized to the width it has is unchanged. -/
private theorem resizeCount_self {w : Nat} (c : LLVM.Int w) : resizeCount w c = c := by
  simp only [resizeCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  split <;> rfl

/-- The integer a byte casts to when the poison bits of `b` are frozen to `bits`: poison if every
bit of `b` is (see `Builtin.byteToIntCTree`). With `bits = 0`, it is `LLVM.Byte.toFrozenInt b`. -/
def freezeByteWith {w : Nat} (b : LLVM.Byte w) (bits : BitVec w) : LLVM.Int w :=
  if b.poison = BitVec.allOnes w then .poison else .val (b.val ||| (b.poison &&& bits))

/-- An integer cast to a byte and back is unchanged, at a nonzero width, whatever bits the cast
back chooses. -/
private theorem freezeByteWith_fromInt {w : Nat} (h : 0 < w) (x : LLVM.Int w) (bits : BitVec w) :
    freezeByteWith (LLVM.Byte.fromInt x) bits = x := by
  cases x <;> simp [freezeByteWith, LLVM.Byte.fromInt, LLVM.Int.isPoison] <;> grind

/-- `llvm.trunc` of a byte, through the integer of its bits, without the flags that LLVM ignores on
bytes, whatever bits the cast to the integer chooses. -/
private theorem byte_trunc_frozen {w w' : Nat} (h : w > w') (b : LLVM.Byte w) (bits : BitVec w) :
    LLVM.Byte.isRefinedBy (b.trunc w')
      (LLVM.Byte.fromInt ((freezeByteWith b bits).trunc w' false false h)) := by
  simp only [LLVM.Byte.isRefinedBy, LLVM.Byte.fromInt, freezeByteWith, BitVec.ofNat_eq_ofNat]
  veir_bv_normalize
  split
  · case _ h =>
    ext k hk
    simp [h]
    omega
  · case _ h =>
    ext k hk
    simp
    by_cases hp : b.poison.getLsbD k <;> simp [hp]

private theorem shiftAmount_val {w : Nat} (y : BitVec w) :
    shiftAmount w (.val y) = if y.toNat < w then .val y else .val (BitVec.allOnes w) := by
  simp only [shiftAmount]
  split <;> simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem not_ge_of_lt {w : Nat} {y : BitVec w} (h : y.toNat < w) : ¬ y ≥ (w : BitVec w) := by
  rw [ge_iff_le, BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  omega

private theorem ge_of_not_lt {w : Nat} {y : BitVec w} (h : ¬ y.toNat < w) : y ≥ (w : BitVec w) := by
  rw [ge_iff_le, BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  omega

private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- Closes the bitwise goals left by the byte shift cases. -/
local macro "byte_shift_tac" y:ident : tactic => `(tactic| (
  all_goals try simp_all [id_pure, LLVM.Byte.allPoison, LLVM.Int.isPoison]
  all_goals (ext k hk; try simp_all)
  all_goals (by_cases hlt : k < ($y).toNat <;> simp [hlt])))

/-- The frozen integer of a byte that is not entirely poison is its bits. -/
private theorem toFrozenInt_of_ne {w : Nat} {b : LLVM.Byte w} (hb : b.poison ≠ BitVec.allOnes w) :
    _root_.LLVM.Byte.toFrozenInt b = .val b.val := by
  simp [_root_.LLVM.Byte.toFrozenInt, hb]

/-- `llvm.shl` of a byte that is not entirely poison, through the integer of its bits. -/
private theorem byte_shl_frozen {w : Nat} (b : LLVM.Byte w) (y : LLVM.Int w) (nuw : Bool)
    (hb : b.poison ≠ BitVec.allOnes w) :
    LLVM.Byte.isRefinedBy (b.shl y nuw)
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).shl (shiftAmount w y) false nuw)) := by
  rw [toFrozenInt_of_ne hb]
  cases y with
  | poison =>
    simp only [LLVM.Byte.shl, Id.run]
    exact LLVM.Byte.allPoison_isRefinedBy _
  | val y =>
    rw [shiftAmount_val]
    by_cases hy : y.toNat < w
    · simp only [hy, ite_true]
      cases nuw <;>
        simp [LLVM.Byte.shl, LLVM.Int.shl, Id.run, LLVM.Byte.fromInt] <;>
        (try split) <;> (try split) <;> (try split) <;>
        byte_shift_tac y
    · simp only [LLVM.Byte.shl, Id.run, ge_of_not_lt hy, ite_true]
      exact LLVM.Byte.allPoison_isRefinedBy _

/-- `llvm.lshr` of a byte that is not entirely poison, through the integer of its bits. -/
private theorem byte_lshr_frozen {w : Nat} (b : LLVM.Byte w) (y : LLVM.Int w) (exact : Bool)
    (hb : b.poison ≠ BitVec.allOnes w) :
    LLVM.Byte.isRefinedBy (b.lshr y exact)
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).lshr (shiftAmount w y) exact)) := by
  rw [toFrozenInt_of_ne hb]
  cases y with
  | poison =>
    simp only [LLVM.Byte.lshr, LLVM.Int.isPoison, Bool.true_or, ite_true]
    exact LLVM.Byte.allPoison_isRefinedBy _
  | val y =>
    rw [shiftAmount_val]
    by_cases hy : y.toNat < w
    · simp only [hy, ite_true]
      cases exact <;>
        simp [LLVM.Byte.lshr, LLVM.Int.lshr, Id.run, LLVM.Byte.fromInt,
          LLVM.Int.isPoison, LLVM.Int.getValueD] <;>
        (try split) <;> (try split) <;> (try split) <;>
        byte_shift_tac y
    · simp only [LLVM.Byte.lshr, LLVM.Int.getValueD, ge_of_not_lt hy, decide_true, Bool.or_true,
        ite_true]
      exact LLVM.Byte.allPoison_isRefinedBy _

/-- `llvm.bitcast` of a byte to an integer, at a nonzero width: freezing the poison bits, to any
`bits`, refines the integer, which is poison if any bit is. -/
private theorem byte_toInt_frozen {w : Nat} (hw : 0 < w) (b : LLVM.Byte w) (bits : BitVec w) :
    _root_.isRefinedBy b.toInt (freezeByteWith b bits) := by
  simp only [LLVM.Byte.toInt, freezeByteWith]
  split <;> split
  · rename_i h h'
    rw [h] at h'
    have := congrArg BitVec.toNat h'
    simp [BitVec.toNat_allOnes] at this
    have := Nat.one_lt_two_pow (n := w) (by omega)
    omega
  all_goals first | exact isRefinedBy_refl _ | exact poison_isRefinedBy _ | simp_all

/-- The pointer cast back from the address of an allocation refines it: it is the allocation's
pointer without its provenance. -/
private theorem ptrFromInt_toInt (mem : MemoryState) (p : Pointer) :
    LLVM.Ptr.isRefinedBy (.val p) (mem.ptrFromInt (LLVM.Ptr.toInt (.val p))) := by
  simp only [LLVM.Ptr.isRefinedBy, MemoryState.ptrFromInt, LLVM.Ptr.toInt, MemoryState.decode,
    UInt64.ofBitVec_toBitVec, Pointer.isRefinedBy_iff]

end Veir.LLVMToGMIR.CTreeProofs
