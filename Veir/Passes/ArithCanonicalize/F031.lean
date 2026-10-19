import Veir.Passes.ArithCanonicalize.ConstSupport

/-! `arith.divsi(x, x) -> 1`; undefined source cases refine vacuously. -/

namespace Veir.ArithCanonicalize.F031

open Veir
open Veir.Puddle
open Veir.Data
open Veir.ArithPuddle

private theorem self_div_refines (w : Nat) (x : LLVM.Int w) (exact : Bool)
    (h : LLVM.Int.isSignedDivisionUB x x = false) :
    RuntimeValue.int w (LLVM.Int.sdiv x x exact) ⊒
      .int w (.val (BitVec.ofInt w 1)) := by
  cases x with
  | poison => simp [LLVM.Int.isSignedDivisionUB] at h
  | val bits =>
    have hn : bits ≠ 0#w := by
      have hh := h
      simp [LLVM.Int.isSignedDivisionUB] at hh
      exact hh.1
    have hov : ¬(bits = BitVec.intMin w ∧ bits = -1#w) := by
      have hh := h
      simp [LLVM.Int.isSignedDivisionUB] at hh
      grind
    have hmod : bits.smod bits = 0#w := by
      cases hs : bits.msb <;> simp [BitVec.smod_eq, hs, BitVec.umod_self]
    simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
      Id.run, BitVec.sdiv_self, hn, hov, hmod]

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .divsi) #[x, x] #[ty]
      return ty)
    (fun ty => createConstant ty 1)
    (fun one => one)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, createConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x divProp divVal hinterpDiv
  obtain ⟨hUB, rfl⟩ := (divsi_iff _ _ _ _ _).mp hinterpDiv
  simp only [IsTypeAttr.cast?_of, Option.bind_some]
  refine ⟨.int w (.val (BitVec.ofInt w 1)), ?_, self_div_refines _ _ _ hUB⟩
  apply (constant_iff _ _ _).mpr
  exact congrArg (fun bits => RuntimeValue.int w (LLVM.Int.val bits))
    (ofInt_ofInt (IntegerType.mk w signedness) 1).symm

end Veir.ArithCanonicalize.F031
