module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorComplementaryMasks

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorComplementaryMasksPattern
    (rootCommuted innerCommuted notBConstantLeft notAConstantLeft : Bool) : Pattern OpCode :=
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
      let left ← if innerCommuted && !rootCommuted then
        MatchProg.operation (.llvm .and) #[notB.res[0]!, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[a, notB.res[0]!] #[ty] (fun _ => true)
      let notA ← if notAConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, minusOne] #[ty] (fun _ => true)
      let right ← if innerCommuted && rootCommuted then
        MatchProg.operation (.llvm .and) #[b, notA.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[notA.res[0]!, b] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[right.res[0]!, left.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[left.res[0]!, right.res[0]!] #[ty] (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp)
    (fun result => result.res[0]!)

set_option maxHeartbeats 2000000 in
private theorem xorComplementaryMasksPattern_valid
    (rootCommuted innerCommuted notBConstantLeft notAConstantLeft : Bool) :
    Pattern.Valid (xorComplementaryMasksPattern rootCommuted innerCommuted notBConstantLeft notAConstantLeft) := by
  cases rootCommuted <;> cases innerCommuted <;> cases notBConstantLeft <;>
    cases notAConstantLeft <;>
    simp only [xorComplementaryMasksPattern, matchIntConstantNormalized, Bool.false_eq_true,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
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
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (complementary_masks_xor_refines_xor w a b)

/- Scalar specialization of InstCombineAndOrXor.cpp:4846-4848. -/
public def xorComplementaryMasks : Pattern OpCode :=
  xorComplementaryMasksPattern false false false false

public theorem xorComplementaryMasks_valid : Pattern.Valid xorComplementaryMasks :=
  xorComplementaryMasksPattern_valid false false false false

public def xorLeftCommutedComplementaryMasks : Pattern OpCode :=
  xorComplementaryMasksPattern false true false false

public theorem xorLeftCommutedComplementaryMasks_valid :
    Pattern.Valid xorLeftCommutedComplementaryMasks :=
  xorComplementaryMasksPattern_valid false true false false

public def xorSwappedComplementaryMasks : Pattern OpCode :=
  xorComplementaryMasksPattern true false false false

public theorem xorSwappedComplementaryMasks_valid :
    Pattern.Valid xorSwappedComplementaryMasks :=
  xorComplementaryMasksPattern_valid true false false false

public def xorSwappedCommutedComplementaryMasks : Pattern OpCode :=
  xorComplementaryMasksPattern true true false false

public theorem xorSwappedCommutedComplementaryMasks_valid :
    Pattern.Valid xorSwappedCommutedComplementaryMasks :=
  xorComplementaryMasksPattern_valid true true false false

public def xorComplementaryMasksNotBLeft : Pattern OpCode :=
  xorComplementaryMasksPattern false false true false
public theorem xorComplementaryMasksNotBLeft_valid : Pattern.Valid xorComplementaryMasksNotBLeft :=
  xorComplementaryMasksPattern_valid false false true false

public def xorComplementaryMasksNotALeft : Pattern OpCode :=
  xorComplementaryMasksPattern false false false true
public theorem xorComplementaryMasksNotALeft_valid : Pattern.Valid xorComplementaryMasksNotALeft :=
  xorComplementaryMasksPattern_valid false false false true

public def xorComplementaryMasksBothNotLeft : Pattern OpCode :=
  xorComplementaryMasksPattern false false true true
public theorem xorComplementaryMasksBothNotLeft_valid : Pattern.Valid xorComplementaryMasksBothNotLeft :=
  xorComplementaryMasksPattern_valid false false true true

public def xorLeftCommutedComplementaryMasksNotBLeft : Pattern OpCode :=
  xorComplementaryMasksPattern false true true false
public theorem xorLeftCommutedComplementaryMasksNotBLeft_valid : Pattern.Valid xorLeftCommutedComplementaryMasksNotBLeft :=
  xorComplementaryMasksPattern_valid false true true false

public def xorLeftCommutedComplementaryMasksNotALeft : Pattern OpCode :=
  xorComplementaryMasksPattern false true false true
public theorem xorLeftCommutedComplementaryMasksNotALeft_valid : Pattern.Valid xorLeftCommutedComplementaryMasksNotALeft :=
  xorComplementaryMasksPattern_valid false true false true

public def xorLeftCommutedComplementaryMasksBothNotLeft : Pattern OpCode :=
  xorComplementaryMasksPattern false true true true
public theorem xorLeftCommutedComplementaryMasksBothNotLeft_valid : Pattern.Valid xorLeftCommutedComplementaryMasksBothNotLeft :=
  xorComplementaryMasksPattern_valid false true true true

public def xorSwappedComplementaryMasksNotBLeft : Pattern OpCode :=
  xorComplementaryMasksPattern true false true false
public theorem xorSwappedComplementaryMasksNotBLeft_valid : Pattern.Valid xorSwappedComplementaryMasksNotBLeft :=
  xorComplementaryMasksPattern_valid true false true false

public def xorSwappedComplementaryMasksNotALeft : Pattern OpCode :=
  xorComplementaryMasksPattern true false false true
public theorem xorSwappedComplementaryMasksNotALeft_valid : Pattern.Valid xorSwappedComplementaryMasksNotALeft :=
  xorComplementaryMasksPattern_valid true false false true

public def xorSwappedComplementaryMasksBothNotLeft : Pattern OpCode :=
  xorComplementaryMasksPattern true false true true
public theorem xorSwappedComplementaryMasksBothNotLeft_valid : Pattern.Valid xorSwappedComplementaryMasksBothNotLeft :=
  xorComplementaryMasksPattern_valid true false true true

public def xorSwappedCommutedComplementaryMasksNotBLeft : Pattern OpCode :=
  xorComplementaryMasksPattern true true true false
public theorem xorSwappedCommutedComplementaryMasksNotBLeft_valid : Pattern.Valid xorSwappedCommutedComplementaryMasksNotBLeft :=
  xorComplementaryMasksPattern_valid true true true false

public def xorSwappedCommutedComplementaryMasksNotALeft : Pattern OpCode :=
  xorComplementaryMasksPattern true true false true
public theorem xorSwappedCommutedComplementaryMasksNotALeft_valid : Pattern.Valid xorSwappedCommutedComplementaryMasksNotALeft :=
  xorComplementaryMasksPattern_valid true true false true

public def xorSwappedCommutedComplementaryMasksBothNotLeft : Pattern OpCode :=
  xorComplementaryMasksPattern true true true true
public theorem xorSwappedCommutedComplementaryMasksBothNotLeft_valid : Pattern.Valid xorSwappedCommutedComplementaryMasksBothNotLeft :=
  xorComplementaryMasksPattern_valid true true true true

end Veir.Passes.InstCombineLLVM.XorComplementaryMasks

#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasks_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorComplementaryMasksBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorLeftCommutedComplementaryMasksBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedComplementaryMasksBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryMasks.xorSwappedCommutedComplementaryMasksBothNotLeft_valid
