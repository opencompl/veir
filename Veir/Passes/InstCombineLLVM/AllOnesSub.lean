module

public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AllOnesSub

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:2531-2533: `(-1)-A -> ~A`. -/
public def allOnesSubToNot : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let _ ← MatchProg.root (.llvm .sub) #[minusOne, x] #[ty] (fun _ => true)
      return (ty, x, minusOne))
    (fun (ty, x, minusOne) => do
      let props ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[x, minusOne] #[ty] props)
    (fun result => result.res[0]!)

public theorem allOnesSubToNot_valid : Pattern.Valid allOnesSubToNot := by
  simp only [allOnesSubToNot, matchIntConstantNormalized]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index,
    forall_eq_apply_imp_iff]
  rintro ⟨w, signedness⟩ x
  rintro ⟨constantValue⟩ minusOne hInterpMinusOne
  cases constantValue with
  | float _ | dense _ | string _ =>
    rintro _ _ _ hMinusOne
    simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
  | integer minusOneAttr =>
    obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
    rintro subProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rintro hMinusOne
    have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
      simpa [isNormalizedIntConstant, asLLVMConstantProperties,
        IsTypeAttr.cast?_of] using hMinusOne
    rw [hMinusOneBits]
    refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))), ?_, ?_⟩
    · exact (xor_iff _ _ _ _).mpr rfl
    change ∃ h : w = w,
      (LLVM.Int.sub (.val (BitVec.ofInt w (-1))) x subProps.nsw subProps.nuw).cast h ⊒
        LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (allOnes_sub_refines_not w x subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.AllOnesSub
