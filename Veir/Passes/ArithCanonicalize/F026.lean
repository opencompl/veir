import Veir.Dialects.Arith.Puddle

/-! `arith.divui(x, x) -> 1`; zero divisor is undefined. -/

namespace Veir.ArithCanonicalize.F026

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

private theorem self_div_refines (w : Nat) (x : LLVM.Int w) (exact : Bool)
    (h : LLVM.Int.isUnsignedDivisionUB x = false) :
    RuntimeValue.int w (LLVM.Int.udiv x x exact) ⊒
      .int w (.val (BitVec.ofInt w 1)) := by
  cases x with
  | poison => simp [LLVM.Int.isUnsignedDivisionUB] at h
  | val bits =>
    have hn : bits ≠ 0#w := by
      simpa [LLVM.Int.isUnsignedDivisionUB] using h
    simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv, isRefinedBy,
      Id.run, BitVec.udiv_self, hn]

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .divui) #[x, x] #[ty]
      return ty)
    (fun ty => createConstant ty 1)
    (fun one => one)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, createConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x divProp divVal hinterpDiv
  obtain ⟨hUB, rfl⟩ := (divui_iff _ _ _ _ _).mp hinterpDiv
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val (BitVec.ofInt w 1)), ?_, self_div_refines _ _ _ hUB⟩
  apply (constant_iff _ _ _).mpr
  simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
  split
  · apply BitVec.eq_of_toNat_eq
    change (1 % Int.ofNat (2 ^ w)).toNat =
      ((1 % Int.ofNat (2 ^ w)) % Int.ofNat (2 ^ w)).toNat
    rw [Int.emod_emod]
  · simp

end Veir.ArithCanonicalize.F026
