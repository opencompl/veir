module

public import Veir.Passes.InstCombineLLVM.SelectSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SelectAbsorbNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def pattern (constantLeft : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let valueTy ← MatchProg.type (Attr := IntegerType)
    let condition ← MatchProg.value condTy
    let trueValue ← MatchProg.value valueTy
    let falseValue ← MatchProg.value valueTy
    let one ← matchSelectConstant condTy 1
    let notCondition ← MatchProg.operation (.llvm .xor)
      (if constantLeft then #[one, condition] else #[condition, one]) #[condTy]
      (fun _ => true)
    let _ ← MatchProg.root (.llvm .select)
      #[notCondition.res[0]!, trueValue, falseValue] #[valueTy] (fun _ => true)
    return (valueTy, condition, trueValue, falseValue))
  (fun (valueTy, condition, trueValue, falseValue) => do
    let properties ← CreateProg.property (.llvm .select) ()
    CreateProg.operation (.llvm .select) #[condition, falseValue, trueValue]
      #[valueTy] properties)
  (fun result => result.res[0]!)

private theorem valid (constantLeft : Bool) : Pattern.Valid (pattern constantLeft) := by
  cases constantLeft <;> simp only [pattern, Bool.false_eq_true, Bool.true_eq,
    ite_false, ite_true, matchSelectConstant] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro condType ⟨condW, condSignedness⟩ hCondType hCondWidth
    subst condType
    change condW = 1 at hCondWidth
    subst condW
    rintro ⟨valueW, valueSignedness⟩
    rintro condition hCondition trueValue hTrue falseValue hFalse
    obtain ⟨condition, rfl⟩ := RuntimeValue.Conforms.integerType.mp hCondition
    obtain ⟨trueValue, rfl⟩ := RuntimeValue.Conforms.integerType.mp hTrue
    obtain ⟨falseValue, rfl⟩ := RuntimeValue.Conforms.integerType.mp hFalse
    rintro property constant hConstant hConstantInterp
    let property' : LLVMConstantProperties := asLLVMConstantProperties property
    change (match property'.value with
      | .integer attr => decide (attr.value = 1)
      | _ => false) = true at hConstant
    change InterpretsTo (.llvm .mlir__constant) property'
      #[IntegerType.mk 1 condSignedness] #[] #[constant] at hConstantInterp
    rcases property' with ⟨constantValue⟩
    cases constantValue with
    | float _ | dense _ | string _ => simp at hConstant
    | integer attr =>
      simp at hConstant
      obtain rfl := (constant_iff _ attr _).mp hConstantInterp
      rintro ⟨⟩ notCondition hNotCondition
      obtain rfl := (xor_iff _ _ _ _).mp hNotCondition
      rintro ⟨⟩ source hSource
      obtain rfl := (select_iff _ _ _ _ _).mp hSource
      refine ⟨.int valueW (LLVM.Int.select condition falseValue trueValue),
        (select_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [hConstant]
      first
      | (have hEq := select_not_swap condition trueValue falseValue
         simp only [i1one, i1not] at hEq
         rw [hEq]
         simp only [LLVM.Int.cast_self, isRefinedBy_refl])
      | (rw [llvm_xor_comm (.val (BitVec.ofInt 1 1)) condition]
         have hEq := select_not_swap condition trueValue falseValue
         simp only [i1one, i1not] at hEq
         rw [hEq]
         simp only [LLVM.Int.cast_self, isRefinedBy_refl])

/-- Scalar specialization with the canonical `xor condition, 1` NOT form. -/
public def selectAbsorbNot : Pattern OpCode := pattern false

public theorem selectAbsorbNot_valid : Pattern.Valid selectAbsorbNot := valid false

/-- Source `m_Not` variant with the normalized i1 all-ones constant on the left. -/
public def selectAbsorbNotConstantLeft : Pattern OpCode := pattern true

public theorem selectAbsorbNotConstantLeft_valid :
    Pattern.Valid selectAbsorbNotConstantLeft := valid true

end Veir.Passes.InstCombineLLVM.SelectAbsorbNot
