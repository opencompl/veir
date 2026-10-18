module

public import Veir.Passes.InstCombineLLVM.SelectSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SelectDeMorganOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private theorem oriented (leftA leftB : Bool) (a b : LLVM.Int 1) :
    LLVM.Int.select
        (if leftA then LLVM.Int.xor i1one a else LLVM.Int.xor a i1one)
        i1one
        (if leftB then LLVM.Int.xor i1one b else LLVM.Int.xor b i1one) =
      LLVM.Int.xor (LLVM.Int.select a b i1zero) i1one := by
  cases leftA <;> cases leftB <;>
    simpa only [Bool.false_eq_true, ite_false, ite_true, i1not,
      llvm_xor_comm i1one] using select_demorgan_or a b

private def pattern (leftA leftB : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let oneA ← matchSelectConstant ty 1
    let notA ← MatchProg.operation (.llvm .xor)
      (if leftA then #[oneA, a] else #[a, oneA]) #[ty] (fun _ => true)
    let oneB ← matchSelectConstant ty 1
    let notB ← MatchProg.operation (.llvm .xor)
      (if leftB then #[oneB, b] else #[b, oneB]) #[ty] (fun _ => true)
    let rootOne ← matchSelectConstant ty 1
    let root ← MatchProg.root (.llvm .select)
      #[notA.res[0]!, rootOne, notB.res[0]!] #[ty] (fun _ => true)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 3)
      let notAValue := operands[0]!
      let notBValue := operands[2]!
      let some useA := notAValue.getFirstUse! ctx | none
      let some useB := notBValue.getFirstUse! ctx | none
      guard ((useA.getNextUse! ctx).isNone || (useB.getNextUse! ctx).isNone))
    return (ty, a, b, rootOne))
  (fun (ty, a, b, one) => do
    let zeroProperties ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty (selectConstantProperty 0)
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty]
      zeroProperties
    let selectProperties ← CreateProg.property (.llvm .select) ()
    let logicalAnd ← CreateProg.operation (.llvm .select) #[a, b, zero.res[0]!]
      #[ty] selectProperties
    let xorProperties ← CreateProg.property (.llvm .xor) ()
    CreateProg.operation (.llvm .xor) #[logicalAnd.res[0]!, one]
      #[ty] xorProperties)
  (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem valid (leftA leftB : Bool) : Pattern.Valid (pattern leftA leftB) := by
  cases leftA <;> cases leftB <;> simp only [pattern, Bool.false_eq_true,
    Bool.true_eq, ite_false, ite_true, matchSelectConstant] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro propertyA constantA hConstantA hConstantAInterp
    let propertyA' : LLVMConstantProperties := asLLVMConstantProperties propertyA
    change (match propertyA'.value with
      | .integer attr => decide (attr.value = 1)
      | _ => false) = true at hConstantA
    change InterpretsTo (.llvm .mlir__constant) propertyA'
      #[IntegerType.mk 1 signedness] #[] #[constantA] at hConstantAInterp
    rcases propertyA' with ⟨valueA⟩
    cases valueA with
    | float _ | dense _ | string _ => simp at hConstantA
    | integer attrA =>
      simp at hConstantA
      obtain rfl := (constant_iff _ attrA _).mp hConstantAInterp
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro propertyB constantB hConstantB hConstantBInterp
      let propertyB' : LLVMConstantProperties := asLLVMConstantProperties propertyB
      change (match propertyB'.value with
        | .integer attr => decide (attr.value = 1)
        | _ => false) = true at hConstantB
      change InterpretsTo (.llvm .mlir__constant) propertyB'
        #[IntegerType.mk 1 signedness] #[] #[constantB] at hConstantBInterp
      rcases propertyB' with ⟨valueB⟩
      cases valueB with
      | float _ | dense _ | string _ => simp at hConstantB
      | integer attrB =>
        simp at hConstantB
        obtain rfl := (constant_iff _ attrB _).mp hConstantBInterp
        rintro ⟨⟩ notB hNotB
        obtain rfl := (xor_iff _ _ _ _).mp hNotB
        rintro propertyZero constantZero hZero hZeroInterp
        let propertyZero' : LLVMConstantProperties := asLLVMConstantProperties propertyZero
        change (match propertyZero'.value with
          | .integer attr => decide (attr.value = 1)
          | _ => false) = true at hZero
        change InterpretsTo (.llvm .mlir__constant) propertyZero'
          #[IntegerType.mk 1 signedness] #[] #[constantZero] at hZeroInterp
        rcases propertyZero' with ⟨zeroValue⟩
        cases zeroValue with
        | float _ | dense _ | string _ => simp at hZero
        | integer attrZero =>
          simp at hZero
          obtain rfl := (constant_iff _ attrZero _).mp hZeroInterp
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
          refine ⟨.int 1 (LLVM.Int.select a b
            (.val (BitVec.ofInt 1 0))),
            (select_iff _ _ _ _ _).mpr rfl, ?_⟩
          refine ⟨.int 1 (LLVM.Int.xor
            (LLVM.Int.select a b (.val (BitVec.ofInt 1 0)))
            (.val (BitVec.ofInt 1 attrZero.value))),
            (xor_iff _ _ _ _).mpr rfl, ?_⟩
          refine ⟨rfl, ?_⟩
          rw [hConstantA, hConstantB, hZero]
          simp only [LLVM.Int.cast_self]
          first
          | (have hEq := oriented false false a b
             simp only [Bool.false_eq_true, ite_false, i1one, i1zero] at hEq
             rw [hEq]
             simp only [isRefinedBy_refl])
          | (have hEq := oriented false true a b
             simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
               i1one, i1zero] at hEq
             rw [hEq]
             simp only [isRefinedBy_refl])
          | (have hEq := oriented true false a b
             simp only [Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
               i1one, i1zero] at hEq
             rw [hEq]
             simp only [isRefinedBy_refl])
          | (have hEq := oriented true true a b
             simp only [Bool.true_eq, ite_true, i1one, i1zero] at hEq
             rw [hEq]
             simp only [isRefinedBy_refl])

public def selectDeMorganOr : Pattern OpCode := pattern false false
public theorem selectDeMorganOr_valid : Pattern.Valid selectDeMorganOr := valid false false

public def selectDeMorganOrNotBLeft : Pattern OpCode := pattern false true
public theorem selectDeMorganOrNotBLeft_valid : Pattern.Valid selectDeMorganOrNotBLeft :=
  valid false true

public def selectDeMorganOrNotALeft : Pattern OpCode := pattern true false
public theorem selectDeMorganOrNotALeft_valid : Pattern.Valid selectDeMorganOrNotALeft :=
  valid true false

public def selectDeMorganOrBothLeft : Pattern OpCode := pattern true true
public theorem selectDeMorganOrBothLeft_valid : Pattern.Valid selectDeMorganOrBothLeft :=
  valid true true

end Veir.Passes.InstCombineLLVM.SelectDeMorganOr
