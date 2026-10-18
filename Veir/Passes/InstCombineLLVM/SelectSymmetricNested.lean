module

public import Veir.Passes.InstCombineLLVM.SelectSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SelectSymmetricNested

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- Scalar specialization of InstCombineSelect.cpp:3694-3709. The contextual
    inspection implements both source `m_OneUse` guards on the inner selects. -/
public def selectSymmetricNested : Pattern OpCode := Pattern.Builder
  (do
    let condTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let valueTy ← MatchProg.type (Attr := IntegerType)
    let innerCondition ← MatchProg.value condTy
    let outerCondition ← MatchProg.value condTy
    let a ← MatchProg.value valueTy
    let b ← MatchProg.value valueTy
    let inner ← MatchProg.operation (.llvm .select) #[innerCondition, a, b]
      #[valueTy] (fun _ => true)
    let swapped ← MatchProg.operation (.llvm .select) #[innerCondition, b, a]
      #[valueTy] (fun _ => true)
    let root ← MatchProg.root (.llvm .select)
      #[outerCondition, inner.res[0]!, swapped.res[0]!] #[valueTy] (fun _ => true)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 3)
      let trueValue := operands[1]!
      let falseValue := operands[2]!
      let some trueUse := trueValue.getFirstUse! ctx | none
      let some falseUse := falseValue.getFirstUse! ctx | none
      guard ((trueUse.getNextUse! ctx).isNone)
      guard ((falseUse.getNextUse! ctx).isNone))
    return (condTy, valueTy, innerCondition, outerCondition, a, b))
  (fun (condTy, valueTy, innerCondition, outerCondition, a, b) => do
    let xorProperties ← CreateProg.property (.llvm .xor) ()
    let xor ← CreateProg.operation (.llvm .xor) #[innerCondition, outerCondition]
      #[condTy] xorProperties
    let selectProperties ← CreateProg.property (.llvm .select) ()
    CreateProg.operation (.llvm .select) #[xor.res[0]!, b, a]
      #[valueTy] selectProperties)
  (fun result => result.res[0]!)

public theorem selectSymmetricNested_valid : Pattern.Valid selectSymmetricNested := by
  simp only [selectSymmetricNested]
  unfoldPuddleBuilder
  proveScalarPuddleStructure
  simpPuddleSemantics
  rintro condType ⟨condW, condSignedness⟩ hCondType hCondWidth
  subst condType
  change condW = 1 at hCondWidth
  subst condW
  rintro ⟨valueW, valueSignedness⟩
  rintro innerCondition hInnerCondition outerCondition hOuterCondition a hA b hB
  obtain ⟨innerCondition, rfl⟩ := RuntimeValue.Conforms.integerType.mp hInnerCondition
  obtain ⟨outerCondition, rfl⟩ := RuntimeValue.Conforms.integerType.mp hOuterCondition
  obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
  obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
  rintro ⟨⟩ inner hInner
  obtain rfl := (select_iff _ _ _ _ _).mp hInner
  rintro ⟨⟩ swapped hSwapped
  obtain rfl := (select_iff _ _ _ _ _).mp hSwapped
  rintro ⟨⟩ source hSource
  obtain rfl := (select_iff _ _ _ _ _).mp hSource
  rintro ⟨⟩
  refine ⟨.int 1 (LLVM.Int.xor innerCondition outerCondition),
    (xor_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨.int valueW
    (LLVM.Int.select (LLVM.Int.xor innerCondition outerCondition) b a),
    (select_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  have hEq := select_symmetric innerCondition outerCondition a b
  rw [hEq]
  simp only [LLVM.Int.cast_self, isRefinedBy_refl]

end Veir.Passes.InstCombineLLVM.SelectSymmetricNested
