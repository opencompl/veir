module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.OrComplementaryMasks

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def orComplementaryMasksPattern
    (leftCommuted rightCommuted notBConstantLeft notAConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notB ← if notBConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, b] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[b, minusOne] #[ty] (fun _ => true)
      let left ← if leftCommuted then
        MatchProg.operation (.llvm .and) #[notB.res[0]!, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[a, notB.res[0]!] #[ty] (fun _ => true)
      let notA ← if notAConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, minusOne] #[ty] (fun _ => true)
      let right ← if rightCommuted then
        MatchProg.operation (.llvm .and) #[b, notA.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[notA.res[0]!, b] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .or) #[left.res[0]!, right.res[0]!] #[ty]
        (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp)
    (fun result => result.res[0]!)

set_option maxHeartbeats 2000000 in
private theorem orComplementaryMasksPattern_valid
    (leftCommuted rightCommuted notBConstantLeft notAConstantLeft : Bool) :
    Pattern.Valid (orComplementaryMasksPattern leftCommuted rightCommuted notBConstantLeft notAConstantLeft) := by
  cases leftCommuted <;> cases rightCommuted <;> cases notBConstantLeft <;>
    cases notAConstantLeft <;>
    simp only [orComplementaryMasksPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.requireBindings, MetadataTuple.Shape.insertFreshBindings,
        IsMetadataTuple.shape_property, CreateProg.checkBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
    simpScalarPropertyPuddleSemantics
    rintro ⟨w, s⟩ a b
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      simp [isNormalizedIntConstant, asLLVMConstantProperties]
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notB hNotB
      obtain rfl := (xor_iff _ _ _ _).mp hNotB
      rintro ⟨⟩ left hLeft
      obtain rfl := (and_iff _ _ _ _).mp hLeft
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro ⟨⟩ right hRight
      obtain rfl := (and_iff _ _ _ _).mp hRight
      rintro orProps source hSource
      obtain rfl := (or_iff _ _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (complementary_masks_or_refines_xor w a b orProps.disjoint)

/-- Scalar specialization of InstCombineAndOrXor.cpp:1993-1999:
    `(A and ~B) or (~A and B) -> A xor B`. -/
public def orComplementaryMasks : Pattern OpCode :=
  orComplementaryMasksPattern false false false false

public theorem orComplementaryMasks_valid : Pattern.Valid orComplementaryMasks :=
  orComplementaryMasksPattern_valid false false false false

/-- Variant with the left `and` operands commuted. -/
public def orLeftCommutedComplementaryMasks : Pattern OpCode :=
  orComplementaryMasksPattern true false false false

public theorem orLeftCommutedComplementaryMasks_valid :
    Pattern.Valid orLeftCommutedComplementaryMasks :=
  orComplementaryMasksPattern_valid true false false false

/-- Variant with the right `and` operands commuted. -/
public def orRightCommutedComplementaryMasks : Pattern OpCode :=
  orComplementaryMasksPattern false true false false

public theorem orRightCommutedComplementaryMasks_valid :
    Pattern.Valid orRightCommutedComplementaryMasks :=
  orComplementaryMasksPattern_valid false true false false

/-- Variant with both source `and` nodes commuted. -/
public def orCommutedComplementaryMasks : Pattern OpCode :=
  orComplementaryMasksPattern true true false false

public theorem orCommutedComplementaryMasks_valid :
    Pattern.Valid orCommutedComplementaryMasks :=
  orComplementaryMasksPattern_valid true true false false

public def orComplementaryMasksNotBLeft : Pattern OpCode :=
  orComplementaryMasksPattern false false true false
public theorem orComplementaryMasksNotBLeft_valid : Pattern.Valid orComplementaryMasksNotBLeft :=
  orComplementaryMasksPattern_valid false false true false

public def orComplementaryMasksNotALeft : Pattern OpCode :=
  orComplementaryMasksPattern false false false true
public theorem orComplementaryMasksNotALeft_valid : Pattern.Valid orComplementaryMasksNotALeft :=
  orComplementaryMasksPattern_valid false false false true

public def orComplementaryMasksBothNotLeft : Pattern OpCode :=
  orComplementaryMasksPattern false false true true
public theorem orComplementaryMasksBothNotLeft_valid : Pattern.Valid orComplementaryMasksBothNotLeft :=
  orComplementaryMasksPattern_valid false false true true

public def orLeftCommutedComplementaryMasksNotBLeft : Pattern OpCode :=
  orComplementaryMasksPattern true false true false
public theorem orLeftCommutedComplementaryMasksNotBLeft_valid : Pattern.Valid orLeftCommutedComplementaryMasksNotBLeft :=
  orComplementaryMasksPattern_valid true false true false

public def orLeftCommutedComplementaryMasksNotALeft : Pattern OpCode :=
  orComplementaryMasksPattern true false false true
public theorem orLeftCommutedComplementaryMasksNotALeft_valid : Pattern.Valid orLeftCommutedComplementaryMasksNotALeft :=
  orComplementaryMasksPattern_valid true false false true

public def orLeftCommutedComplementaryMasksBothNotLeft : Pattern OpCode :=
  orComplementaryMasksPattern true false true true
public theorem orLeftCommutedComplementaryMasksBothNotLeft_valid : Pattern.Valid orLeftCommutedComplementaryMasksBothNotLeft :=
  orComplementaryMasksPattern_valid true false true true

public def orRightCommutedComplementaryMasksNotBLeft : Pattern OpCode :=
  orComplementaryMasksPattern false true true false
public theorem orRightCommutedComplementaryMasksNotBLeft_valid : Pattern.Valid orRightCommutedComplementaryMasksNotBLeft :=
  orComplementaryMasksPattern_valid false true true false

public def orRightCommutedComplementaryMasksNotALeft : Pattern OpCode :=
  orComplementaryMasksPattern false true false true
public theorem orRightCommutedComplementaryMasksNotALeft_valid : Pattern.Valid orRightCommutedComplementaryMasksNotALeft :=
  orComplementaryMasksPattern_valid false true false true

public def orRightCommutedComplementaryMasksBothNotLeft : Pattern OpCode :=
  orComplementaryMasksPattern false true true true
public theorem orRightCommutedComplementaryMasksBothNotLeft_valid : Pattern.Valid orRightCommutedComplementaryMasksBothNotLeft :=
  orComplementaryMasksPattern_valid false true true true

public def orCommutedComplementaryMasksNotBLeft : Pattern OpCode :=
  orComplementaryMasksPattern true true true false
public theorem orCommutedComplementaryMasksNotBLeft_valid : Pattern.Valid orCommutedComplementaryMasksNotBLeft :=
  orComplementaryMasksPattern_valid true true true false

public def orCommutedComplementaryMasksNotALeft : Pattern OpCode :=
  orComplementaryMasksPattern true true false true
public theorem orCommutedComplementaryMasksNotALeft_valid : Pattern.Valid orCommutedComplementaryMasksNotALeft :=
  orComplementaryMasksPattern_valid true true false true

public def orCommutedComplementaryMasksBothNotLeft : Pattern OpCode :=
  orComplementaryMasksPattern true true true true
public theorem orCommutedComplementaryMasksBothNotLeft_valid : Pattern.Valid orCommutedComplementaryMasksBothNotLeft :=
  orComplementaryMasksPattern_valid true true true true

end Veir.Passes.InstCombineLLVM.OrComplementaryMasks

#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orComplementaryMasksBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orLeftCommutedComplementaryMasksBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orRightCommutedComplementaryMasksBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrComplementaryMasks.orCommutedComplementaryMasksBothNotLeft_valid
