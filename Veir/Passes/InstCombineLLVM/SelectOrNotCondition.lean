module

public import Veir.Passes.InstCombineLLVM.SelectSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SelectOrNotCondition

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private theorem oriented (notLeft orSwapped : Bool) (a b c : LLVM.Int 1)
    (disjoint : Bool) :
    LLVM.Int.select
      (if orSwapped then
        LLVM.Int.or c (if notLeft then LLVM.Int.xor i1one a else LLVM.Int.xor a i1one)
          disjoint
       else
        LLVM.Int.or (if notLeft then LLVM.Int.xor i1one a else LLVM.Int.xor a i1one)
          c disjoint) a b ⊒
      LLVM.Int.select a (LLVM.Int.select c i1one b) i1zero := by
  cases notLeft <;> cases orSwapped
  all_goals simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true]
  · exact select_or_not_condition a b c disjoint
  · rw [llvm_or_comm c (i1not a) disjoint]
    exact select_or_not_condition a b c disjoint
  · rw [llvm_xor_comm i1one a]
    exact select_or_not_condition a b c disjoint
  · rw [llvm_xor_comm i1one a, llvm_or_comm c (i1not a) disjoint]
    exact select_or_not_condition a b c disjoint

private def pattern (notLeft orSwapped : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let c ← MatchProg.value ty
    let one ← matchSelectConstant ty 1
    let notA ← MatchProg.operation (.llvm .xor)
      (if notLeft then #[one, a] else #[a, one]) #[ty] (fun _ => true)
    let condition ← MatchProg.operation (.llvm .or)
      (if orSwapped then #[c, notA.res[0]!] else #[notA.res[0]!, c])
      #[ty] (fun _ => true)
    let root ← MatchProg.root (.llvm .select) #[condition.res[0]!, a, b]
      #[ty] (fun _ => true)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 3)
      let conditionValue := operands[0]!
      let some firstUse := conditionValue.getFirstUse! ctx | none
      guard ((firstUse.getNextUse! ctx).isNone))
    return (ty, a, b, c, one))
  (fun (ty, a, b, c, one) => do
    let zeroProperties ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty (selectConstantProperty 0)
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty]
      zeroProperties
    let innerProperties ← CreateProg.property (.llvm .select) ()
    let inner ← CreateProg.operation (.llvm .select) #[c, one, b]
      #[ty] innerProperties
    let outerProperties ← CreateProg.property (.llvm .select) ()
    CreateProg.operation (.llvm .select) #[a, inner.res[0]!, zero.res[0]!]
      #[ty] outerProperties)
  (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem valid (notLeft orSwapped : Bool) : Pattern.Valid (pattern notLeft orSwapped) := by
  cases notLeft <;> cases orSwapped <;> simp only [pattern, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, matchSelectConstant] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB c hC
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    obtain ⟨c, rfl⟩ := RuntimeValue.Conforms.integerType.mp hC
    rintro property constant hConstant hConstantInterp
    let property' : LLVMConstantProperties := asLLVMConstantProperties property
    change (match property'.value with
      | .integer attr => decide (attr.value = 1)
      | _ => false) = true at hConstant
    change InterpretsTo (.llvm .mlir__constant) property'
      #[IntegerType.mk 1 signedness] #[] #[constant] at hConstantInterp
    rcases property' with ⟨constantValue⟩
    cases constantValue with
    | float _ | dense _ | string _ => simp at hConstant
    | integer attr =>
      simp at hConstant
      obtain rfl := (constant_iff _ attr _).mp hConstantInterp
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro orProperties condition hCondition
      obtain rfl := (or_iff _ orProperties _ _ _).mp hCondition
      rintro ⟨⟩ source hSource
      obtain rfl := (select_iff _ _ _ _ _).mp hSource
      rintro ⟨⟩
      simp [selectConstantProperty, IsTypeAttr.cast?_of]
      refine ⟨.int 1 (.val (BitVec.ofInt 1 0)), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int 1 (.val z))
          (ofInt_normalizeValue
            ({ bitwidth := 1, signedness := signedness } : IntegerType) 0).symm
      refine ⟨.int 1 (LLVM.Int.select c (.val (BitVec.ofInt 1 attr.value)) b),
        (select_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int 1 (LLVM.Int.select a
        (LLVM.Int.select c (.val (BitVec.ofInt 1 attr.value)) b)
        (.val (BitVec.ofInt 1 0))), (select_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [hConstant]
      simp only [LLVM.Int.cast_self]
      first
      | exact oriented false false a b c orProperties.disjoint
      | exact oriented false true a b c orProperties.disjoint
      | exact oriented true false a b c orProperties.disjoint
      | exact oriented true true a b c orProperties.disjoint

public def selectOrNotCondition : Pattern OpCode := pattern false false
public theorem selectOrNotCondition_valid : Pattern.Valid selectOrNotCondition := valid false false

public def selectOrNotConditionOrSwapped : Pattern OpCode := pattern false true
public theorem selectOrNotConditionOrSwapped_valid :
    Pattern.Valid selectOrNotConditionOrSwapped := valid false true

public def selectOrNotConditionNotLeft : Pattern OpCode := pattern true false
public theorem selectOrNotConditionNotLeft_valid :
    Pattern.Valid selectOrNotConditionNotLeft := valid true false

public def selectOrNotConditionBothSwapped : Pattern OpCode := pattern true true
public theorem selectOrNotConditionBothSwapped_valid :
    Pattern.Valid selectOrNotConditionBothSwapped := valid true true

end Veir.Passes.InstCombineLLVM.SelectOrNotCondition
