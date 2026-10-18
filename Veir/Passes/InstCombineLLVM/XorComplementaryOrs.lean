module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorComplementaryOrs

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorComplementaryOrsPattern
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
        MatchProg.operation (.llvm .or) #[notB.res[0]!, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[a, notB.res[0]!] #[ty] (fun _ => true)
      let notA ← if notAConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, minusOne] #[ty] (fun _ => true)
      let right ← if innerCommuted && rootCommuted then
        MatchProg.operation (.llvm .or) #[b, notA.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[notA.res[0]!, b] #[ty] (fun _ => true)
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
private theorem xorComplementaryOrsPattern_valid
    (rootCommuted innerCommuted notBConstantLeft notAConstantLeft : Bool) :
    Pattern.Valid (xorComplementaryOrsPattern rootCommuted innerCommuted notBConstantLeft notAConstantLeft) := by
  cases rootCommuted <;> cases innerCommuted <;> cases notBConstantLeft <;>
    cases notAConstantLeft <;>
    simp only [xorComplementaryOrsPattern, matchIntConstantNormalized, Bool.false_eq_true,
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
      rintro leftProps left hLeft
      obtain rfl := (or_iff _ _ _ _ _).mp hLeft
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro rightProps right hRight
      obtain rfl := (or_iff _ _ _ _ _).mp hRight
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (complementary_ors_xor_refines_xor w a b
          leftProps.disjoint rightProps.disjoint)

/- Scalar specialization of InstCombineAndOrXor.cpp:4838-4840. -/
public def xorComplementaryOrs : Pattern OpCode :=
  xorComplementaryOrsPattern false false false false

public theorem xorComplementaryOrs_valid : Pattern.Valid xorComplementaryOrs :=
  xorComplementaryOrsPattern_valid false false false false

public def xorLeftCommutedComplementaryOrs : Pattern OpCode :=
  xorComplementaryOrsPattern false true false false

public theorem xorLeftCommutedComplementaryOrs_valid :
    Pattern.Valid xorLeftCommutedComplementaryOrs :=
  xorComplementaryOrsPattern_valid false true false false

public def xorSwappedComplementaryOrs : Pattern OpCode :=
  xorComplementaryOrsPattern true false false false

public theorem xorSwappedComplementaryOrs_valid :
    Pattern.Valid xorSwappedComplementaryOrs :=
  xorComplementaryOrsPattern_valid true false false false

public def xorSwappedCommutedComplementaryOrs : Pattern OpCode :=
  xorComplementaryOrsPattern true true false false

public theorem xorSwappedCommutedComplementaryOrs_valid :
    Pattern.Valid xorSwappedCommutedComplementaryOrs :=
  xorComplementaryOrsPattern_valid true true false false

public def xorComplementaryOrsNotBLeft : Pattern OpCode :=
  xorComplementaryOrsPattern false false true false
public theorem xorComplementaryOrsNotBLeft_valid : Pattern.Valid xorComplementaryOrsNotBLeft :=
  xorComplementaryOrsPattern_valid false false true false

public def xorComplementaryOrsNotALeft : Pattern OpCode :=
  xorComplementaryOrsPattern false false false true
public theorem xorComplementaryOrsNotALeft_valid : Pattern.Valid xorComplementaryOrsNotALeft :=
  xorComplementaryOrsPattern_valid false false false true

public def xorComplementaryOrsBothNotLeft : Pattern OpCode :=
  xorComplementaryOrsPattern false false true true
public theorem xorComplementaryOrsBothNotLeft_valid : Pattern.Valid xorComplementaryOrsBothNotLeft :=
  xorComplementaryOrsPattern_valid false false true true

public def xorLeftCommutedComplementaryOrsNotBLeft : Pattern OpCode :=
  xorComplementaryOrsPattern false true true false
public theorem xorLeftCommutedComplementaryOrsNotBLeft_valid : Pattern.Valid xorLeftCommutedComplementaryOrsNotBLeft :=
  xorComplementaryOrsPattern_valid false true true false

public def xorLeftCommutedComplementaryOrsNotALeft : Pattern OpCode :=
  xorComplementaryOrsPattern false true false true
public theorem xorLeftCommutedComplementaryOrsNotALeft_valid : Pattern.Valid xorLeftCommutedComplementaryOrsNotALeft :=
  xorComplementaryOrsPattern_valid false true false true

public def xorLeftCommutedComplementaryOrsBothNotLeft : Pattern OpCode :=
  xorComplementaryOrsPattern false true true true
public theorem xorLeftCommutedComplementaryOrsBothNotLeft_valid : Pattern.Valid xorLeftCommutedComplementaryOrsBothNotLeft :=
  xorComplementaryOrsPattern_valid false true true true

public def xorSwappedComplementaryOrsNotBLeft : Pattern OpCode :=
  xorComplementaryOrsPattern true false true false
public theorem xorSwappedComplementaryOrsNotBLeft_valid : Pattern.Valid xorSwappedComplementaryOrsNotBLeft :=
  xorComplementaryOrsPattern_valid true false true false

public def xorSwappedComplementaryOrsNotALeft : Pattern OpCode :=
  xorComplementaryOrsPattern true false false true
public theorem xorSwappedComplementaryOrsNotALeft_valid : Pattern.Valid xorSwappedComplementaryOrsNotALeft :=
  xorComplementaryOrsPattern_valid true false false true

public def xorSwappedComplementaryOrsBothNotLeft : Pattern OpCode :=
  xorComplementaryOrsPattern true false true true
public theorem xorSwappedComplementaryOrsBothNotLeft_valid : Pattern.Valid xorSwappedComplementaryOrsBothNotLeft :=
  xorComplementaryOrsPattern_valid true false true true

public def xorSwappedCommutedComplementaryOrsNotBLeft : Pattern OpCode :=
  xorComplementaryOrsPattern true true true false
public theorem xorSwappedCommutedComplementaryOrsNotBLeft_valid : Pattern.Valid xorSwappedCommutedComplementaryOrsNotBLeft :=
  xorComplementaryOrsPattern_valid true true true false

public def xorSwappedCommutedComplementaryOrsNotALeft : Pattern OpCode :=
  xorComplementaryOrsPattern true true false true
public theorem xorSwappedCommutedComplementaryOrsNotALeft_valid : Pattern.Valid xorSwappedCommutedComplementaryOrsNotALeft :=
  xorComplementaryOrsPattern_valid true true false true

public def xorSwappedCommutedComplementaryOrsBothNotLeft : Pattern OpCode :=
  xorComplementaryOrsPattern true true true true
public theorem xorSwappedCommutedComplementaryOrsBothNotLeft_valid : Pattern.Valid xorSwappedCommutedComplementaryOrsBothNotLeft :=
  xorComplementaryOrsPattern_valid true true true true

end Veir.Passes.InstCombineLLVM.XorComplementaryOrs

#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrs_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorComplementaryOrsBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorLeftCommutedComplementaryOrsBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedComplementaryOrsBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotBLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsNotALeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorComplementaryOrs.xorSwappedCommutedComplementaryOrsBothNotLeft_valid
