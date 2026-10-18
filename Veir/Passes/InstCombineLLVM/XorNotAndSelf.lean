module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorNotAndSelf

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorNotAndSelfPattern (rootCommuted andCommuted notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notA ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[a, minusOne] #[ty] (fun _ => true)
      let and ← if andCommuted then
        MatchProg.operation (.llvm .and) #[b, notA.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[notA.res[0]!, b] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[a, and.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[and.res[0]!, a] #[ty] (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let op ← CreateProg.property (.llvm .or) default
      CreateProg.operation (.llvm .or) #[a, b] #[ty] op)
    (fun result => result.res[0]!)

set_option maxHeartbeats 800000 in
private theorem xorNotAndSelfPattern_valid (rootCommuted andCommuted notConstantLeft : Bool) :
    Pattern.Valid (xorNotAndSelfPattern rootCommuted andCommuted notConstantLeft) := by
  cases rootCommuted <;> cases andCommuted <;> cases notConstantLeft <;>
    simp only [xorNotAndSelfPattern, matchIntConstantNormalized, Bool.false_eq_true, ite_false, ite_true] <;>
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
      rintro ⟨⟩ notA hNotA
      obtain rfl := (xor_iff _ _ _ _).mp hNotA
      rintro ⟨⟩ sourceAnd hAnd
      obtain rfl := (and_iff _ _ _ _).mp hAnd
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.or a b), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (not_and_xor_self_refines_or w a b)

/-- Scalar specialization of InstCombineAndOrXor.cpp:5729-5730:
    `(~A and B) xor A -> A or B`. -/
public def xorNotAndSelf : Pattern OpCode := xorNotAndSelfPattern false false false

public theorem xorNotAndSelf_valid : Pattern.Valid xorNotAndSelf :=
  xorNotAndSelfPattern_valid false false false

/-- Variant with the source `and` operands commuted. -/
public def xorCommutedNotAndSelf : Pattern OpCode := xorNotAndSelfPattern false true false

public theorem xorCommutedNotAndSelf_valid : Pattern.Valid xorCommutedNotAndSelf :=
  xorNotAndSelfPattern_valid false true false

/-- Variant with the root `xor` operands commuted. -/
public def xorSelfNotAnd : Pattern OpCode := xorNotAndSelfPattern true false false

public theorem xorSelfNotAnd_valid : Pattern.Valid xorSelfNotAnd :=
  xorNotAndSelfPattern_valid true false false

/-- Variant with source root and `and` operands commuted. -/
public def xorSelfCommutedNotAnd : Pattern OpCode := xorNotAndSelfPattern true true false

public theorem xorSelfCommutedNotAnd_valid : Pattern.Valid xorSelfCommutedNotAnd :=
  xorNotAndSelfPattern_valid true true false


public def xorNotAndSelfConstantLeft : Pattern OpCode :=
  xorNotAndSelfPattern false false true
public theorem xorNotAndSelfConstantLeft_valid : Pattern.Valid xorNotAndSelfConstantLeft :=
  xorNotAndSelfPattern_valid false false true

public def xorCommutedNotAndSelfConstantLeft : Pattern OpCode :=
  xorNotAndSelfPattern false true true
public theorem xorCommutedNotAndSelfConstantLeft_valid :
    Pattern.Valid xorCommutedNotAndSelfConstantLeft :=
  xorNotAndSelfPattern_valid false true true

public def xorSelfNotAndConstantLeft : Pattern OpCode :=
  xorNotAndSelfPattern true false true
public theorem xorSelfNotAndConstantLeft_valid : Pattern.Valid xorSelfNotAndConstantLeft :=
  xorNotAndSelfPattern_valid true false true

public def xorSelfCommutedNotAndConstantLeft : Pattern OpCode :=
  xorNotAndSelfPattern true true true
public theorem xorSelfCommutedNotAndConstantLeft_valid :
    Pattern.Valid xorSelfCommutedNotAndConstantLeft :=
  xorNotAndSelfPattern_valid true true true

end Veir.Passes.InstCombineLLVM.XorNotAndSelf

#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorNotAndSelf_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorCommutedNotAndSelf_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfNotAnd_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfCommutedNotAnd_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorNotAndSelfConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorCommutedNotAndSelfConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfNotAndConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotAndSelf.xorSelfCommutedNotAndConstantLeft_valid
