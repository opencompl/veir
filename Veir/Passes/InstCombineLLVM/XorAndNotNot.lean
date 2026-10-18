module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorAndNotNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorAndNotNotPattern (andCommuted notBConstantLeft notAConstantLeft : Bool) : Pattern OpCode :=
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
      let and ← if andCommuted then
        MatchProg.operation (.llvm .and) #[notB.res[0]!, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[a, notB.res[0]!] #[ty] (fun _ => true)
      let notA ← if notAConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, minusOne] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .xor) #[and.res[0]!, notA.res[0]!] #[ty] (fun _ => true)
      return (ty, a, b, minusOne))
    (fun (ty, a, b, minusOne) => do
      let ap ← CreateProg.property (.llvm .and) ()
      let and ← CreateProg.operation (.llvm .and) #[a, b] #[ty] ap
      let xp ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[and.res[0]!, minusOne] #[ty] xp)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem xorAndNotNotPattern_valid (andCommuted notBConstantLeft notAConstantLeft : Bool) :
    Pattern.Valid (xorAndNotNotPattern andCommuted notBConstantLeft notAConstantLeft) := by
  cases andCommuted <;> cases notBConstantLeft <;> cases notAConstantLeft <;> simp only [xorAndNotNotPattern, matchIntConstantNormalized,
      Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
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
      rintro ⟨⟩ sourceAnd hAnd
      obtain rfl := (and_iff _ _ _ _).mp hAnd
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.and a b), (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor (LLVM.Int.and a b) (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (and_not_xor_not_refines_not_and w a b)

/-- Scalar specialization of InstCombineAndOrXor.cpp:5724-5726:
    `(A and ~B) xor ~A -> ~(A and B)`. -/
public def xorAndNotNot : Pattern OpCode := xorAndNotNotPattern false false false

public theorem xorAndNotNot_valid : Pattern.Valid xorAndNotNot :=
  xorAndNotNotPattern_valid false false false

/-- Variant with the source `and` operands commuted. -/
public def xorNotAndNot : Pattern OpCode := xorAndNotNotPattern true false false

public theorem xorNotAndNot_valid : Pattern.Valid xorNotAndNot :=
  xorAndNotNotPattern_valid true false false

public def xorAndNotNotFirstNotLeft : Pattern OpCode :=
  xorAndNotNotPattern false true false
public theorem xorAndNotNotFirstNotLeft_valid : Pattern.Valid xorAndNotNotFirstNotLeft :=
  xorAndNotNotPattern_valid false true false

public def xorAndNotNotSecondNotLeft : Pattern OpCode :=
  xorAndNotNotPattern false false true
public theorem xorAndNotNotSecondNotLeft_valid : Pattern.Valid xorAndNotNotSecondNotLeft :=
  xorAndNotNotPattern_valid false false true

public def xorAndNotNotBothNotLeft : Pattern OpCode :=
  xorAndNotNotPattern false true true
public theorem xorAndNotNotBothNotLeft_valid : Pattern.Valid xorAndNotNotBothNotLeft :=
  xorAndNotNotPattern_valid false true true

public def xorNotAndNotFirstNotLeft : Pattern OpCode :=
  xorAndNotNotPattern true true false
public theorem xorNotAndNotFirstNotLeft_valid : Pattern.Valid xorNotAndNotFirstNotLeft :=
  xorAndNotNotPattern_valid true true false

public def xorNotAndNotSecondNotLeft : Pattern OpCode :=
  xorAndNotNotPattern true false true
public theorem xorNotAndNotSecondNotLeft_valid : Pattern.Valid xorNotAndNotSecondNotLeft :=
  xorAndNotNotPattern_valid true false true

public def xorNotAndNotBothNotLeft : Pattern OpCode :=
  xorAndNotNotPattern true true true
public theorem xorNotAndNotBothNotLeft_valid : Pattern.Valid xorNotAndNotBothNotLeft :=
  xorAndNotNotPattern_valid true true true

end Veir.Passes.InstCombineLLVM.XorAndNotNot

#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNot_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNot_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotFirstNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotSecondNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorAndNotNotBothNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotFirstNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotSecondNotLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorAndNotNot.xorNotAndNotBothNotLeft_valid
