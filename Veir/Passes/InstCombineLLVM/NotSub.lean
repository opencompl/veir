module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotSub

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Scalar semantic specialization of InstCombineAndOrXor.cpp:5345-5347:
    `~(X - Y) -> ~X + Y`. -/
private def notSubPattern (notConstantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let minusOne ← matchIntConstantNormalized ty (-1)
    let difference ← MatchProg.operation (.llvm .sub) #[x, y] #[ty] (fun _ => true)
    let _ ← if notConstantLeft then
      MatchProg.root (.llvm .xor) #[minusOne, difference.res[0]!] #[ty] (fun _ => true)
    else
      MatchProg.root (.llvm .xor) #[difference.res[0]!, minusOne] #[ty] (fun _ => true)
    return (ty, x, y, minusOne))
  (fun (ty, x, y, minusOne) => do
    let xp ← CreateProg.property (.llvm .xor) ()
    let notX ← CreateProg.operation (.llvm .xor) #[x, minusOne] #[ty] xp
    let ap ← CreateProg.property (.llvm .add) default
    CreateProg.operation (.llvm .add) #[notX.res[0]!, y] #[ty] ap)
  (fun result => result.res[0]!)

private theorem notSubPattern_valid (notConstantLeft : Bool) :
    Pattern.Valid (notSubPattern notConstantLeft) := by
  cases notConstantLeft <;> simp only [notSubPattern, matchIntConstantNormalized,
    Bool.false_eq_true, ite_false, ite_true] <;>
  unfoldPuddleBuilder
  all_goals proveScalarPuddleStructure
  all_goals simpScalarPuddleSemantics
  all_goals
    rintro ⟨w, signedness⟩ x y
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro subProps difference hDifference
      obtain rfl := (sub_iff _ _ _ _ _).mp hDifference
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.add
          (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y),
        (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        (not_sub_refines_not_add w x y subProps.nsw subProps.nuw)


public def notSub : Pattern OpCode := notSubPattern false
public theorem notSub_valid : Pattern.Valid notSub := notSubPattern_valid false

public def notSubConstantLeft : Pattern OpCode := notSubPattern true
public theorem notSubConstantLeft_valid : Pattern.Valid notSubConstantLeft :=
  notSubPattern_valid true

end Veir.Passes.InstCombineLLVM.NotSub
