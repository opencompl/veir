module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotAndNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def notAndNotPattern (andCommuted innerNotConstantLeft rootNotConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if innerNotConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let both ← if andCommuted then
        MatchProg.operation (.llvm .and) #[y, notX.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[notX.res[0]!, y] #[ty] (fun _ => true)
      let _ ← if rootNotConstantLeft then
        MatchProg.root (.llvm .xor) #[minusOne, both.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[both.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, y, minusOne))
    (fun (ty, x, y, minusOne) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
      let op ← CreateProg.property (.llvm .or) default
      CreateProg.operation (.llvm .or) #[x, notY.res[0]!] #[ty] op)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem notAndNotPattern_valid (andCommuted innerNotConstantLeft rootNotConstantLeft : Bool) :
    Pattern.Valid (notAndNotPattern andCommuted innerNotConstantLeft rootNotConstantLeft) := by
  cases andCommuted <;> cases innerNotConstantLeft <;> cases rootNotConstantLeft <;> simp only [notAndNotPattern, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ x y
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.or x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) false),
        (or_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (not_not_and_refines_or_not w x y)

/- Scalar semantic specialization of InstCombineAndOrXor.cpp:5268-5270.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def notAndNot : Pattern OpCode := notAndNotPattern false false false

public theorem notAndNot_valid : Pattern.Valid notAndNot :=
  notAndNotPattern_valid false false false

public def notCommutedAndNot : Pattern OpCode := notAndNotPattern true false false

public theorem notCommutedAndNot_valid : Pattern.Valid notCommutedAndNot :=
  notAndNotPattern_valid true false false

public def notAndNotFirstNotLeft : Pattern OpCode :=
  notAndNotPattern false true false
public theorem notAndNotFirstNotLeft_valid : Pattern.Valid notAndNotFirstNotLeft :=
  notAndNotPattern_valid false true false

public def notAndNotSecondNotLeft : Pattern OpCode :=
  notAndNotPattern false false true
public theorem notAndNotSecondNotLeft_valid : Pattern.Valid notAndNotSecondNotLeft :=
  notAndNotPattern_valid false false true

public def notAndNotBothNotLeft : Pattern OpCode :=
  notAndNotPattern false true true
public theorem notAndNotBothNotLeft_valid : Pattern.Valid notAndNotBothNotLeft :=
  notAndNotPattern_valid false true true

public def notCommutedAndNotFirstNotLeft : Pattern OpCode :=
  notAndNotPattern true true false
public theorem notCommutedAndNotFirstNotLeft_valid : Pattern.Valid notCommutedAndNotFirstNotLeft :=
  notAndNotPattern_valid true true false

public def notCommutedAndNotSecondNotLeft : Pattern OpCode :=
  notAndNotPattern true false true
public theorem notCommutedAndNotSecondNotLeft_valid : Pattern.Valid notCommutedAndNotSecondNotLeft :=
  notAndNotPattern_valid true false true

public def notCommutedAndNotBothNotLeft : Pattern OpCode :=
  notAndNotPattern true true true
public theorem notCommutedAndNotBothNotLeft_valid : Pattern.Valid notCommutedAndNotBothNotLeft :=
  notAndNotPattern_valid true true true

end Veir.Passes.InstCombineLLVM.NotAndNot
