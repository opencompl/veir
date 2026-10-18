module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NotOrNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def notOrNotPattern (orCommuted innerNotConstantLeft rootNotConstantLeft : Bool) : Pattern OpCode :=
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
      let either ← if orCommuted then
        MatchProg.operation (.llvm .or) #[y, notX.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[notX.res[0]!, y] #[ty] (fun _ => true)
      let _ ← if rootNotConstantLeft then
        MatchProg.root (.llvm .xor) #[minusOne, either.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[either.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, y, minusOne))
    (fun (ty, x, y, minusOne) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne] #[ty] xp
      let ap ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[x, notY.res[0]!] #[ty] ap)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem notOrNotPattern_valid (orCommuted innerNotConstantLeft rootNotConstantLeft : Bool) :
    Pattern.Valid (notOrNotPattern orCommuted innerNotConstantLeft rootNotConstantLeft) := by
  cases orCommuted <;> cases innerNotConstantLeft <;> cases rootNotConstantLeft <;> simp only [notOrNotPattern, matchIntConstantNormalized,
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
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (not_not_or_refines_and_not w x y orProps.disjoint)

/- Scalar semantic specialization of InstCombineAndOrXor.cpp:5282-5284.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def notOrNot : Pattern OpCode := notOrNotPattern false false false

public theorem notOrNot_valid : Pattern.Valid notOrNot :=
  notOrNotPattern_valid false false false

public def notCommutedOrNot : Pattern OpCode := notOrNotPattern true false false

public theorem notCommutedOrNot_valid : Pattern.Valid notCommutedOrNot :=
  notOrNotPattern_valid true false false

public def notOrNotFirstNotLeft : Pattern OpCode :=
  notOrNotPattern false true false
public theorem notOrNotFirstNotLeft_valid : Pattern.Valid notOrNotFirstNotLeft :=
  notOrNotPattern_valid false true false

public def notOrNotSecondNotLeft : Pattern OpCode :=
  notOrNotPattern false false true
public theorem notOrNotSecondNotLeft_valid : Pattern.Valid notOrNotSecondNotLeft :=
  notOrNotPattern_valid false false true

public def notOrNotBothNotLeft : Pattern OpCode :=
  notOrNotPattern false true true
public theorem notOrNotBothNotLeft_valid : Pattern.Valid notOrNotBothNotLeft :=
  notOrNotPattern_valid false true true

public def notCommutedOrNotFirstNotLeft : Pattern OpCode :=
  notOrNotPattern true true false
public theorem notCommutedOrNotFirstNotLeft_valid : Pattern.Valid notCommutedOrNotFirstNotLeft :=
  notOrNotPattern_valid true true false

public def notCommutedOrNotSecondNotLeft : Pattern OpCode :=
  notOrNotPattern true false true
public theorem notCommutedOrNotSecondNotLeft_valid : Pattern.Valid notCommutedOrNotSecondNotLeft :=
  notOrNotPattern_valid true false true

public def notCommutedOrNotBothNotLeft : Pattern OpCode :=
  notOrNotPattern true true true
public theorem notCommutedOrNotBothNotLeft_valid : Pattern.Valid notCommutedOrNotBothNotLeft :=
  notOrNotPattern_valid true true true

end Veir.Passes.InstCombineLLVM.NotOrNot
