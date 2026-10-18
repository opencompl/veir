module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AndOrNotAnd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def andOrNotAndPattern (andCommuted notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let innerOr ← MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let innerAnd ← if andCommuted then
        MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
      let notAnd ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, innerAnd.res[0]!] #[ty]
          (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[innerAnd.res[0]!, minusOne] #[ty]
          (fun _ => true)
      let _ ← MatchProg.root (.llvm .and) #[innerOr.res[0]!, notAnd.res[0]!] #[ty]
        (fun _ => true)
      return (ty, a, b))
    (fun (ty, a, b) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp)
    (fun result => result.res[0]!)

private theorem andOrNotAndPattern_valid (andCommuted notConstantLeft : Bool) :
    Pattern.Valid (andOrNotAndPattern andCommuted notConstantLeft) := by
  cases andCommuted <;> cases notConstantLeft <;>
    simp only [andOrNotAndPattern, matchIntConstantNormalized,
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
      rintro orProps sourceOr hSourceOr
      obtain rfl := (or_iff _ _ _ _ _).mp hSourceOr
      rintro ⟨⟩ sourceAnd hSourceAnd
      obtain rfl := (and_iff _ _ _ _).mp hSourceAnd
      rintro ⟨⟩ notAnd hNotAnd
      obtain rfl := (xor_iff _ _ _ _).mp hNotAnd
      rintro ⟨⟩ source hSource
      obtain rfl := (and_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (or_and_not_and_refines_xor w a b orProps.disjoint)

/-- Scalar specialization of InstCombineAndOrXor.cpp:1954-1956:
    `(A or B) and ~(A and B) -> A xor B`. -/
public def andOrNotAnd : Pattern OpCode := andOrNotAndPattern false false

public theorem andOrNotAnd_valid : Pattern.Valid andOrNotAnd :=
  andOrNotAndPattern_valid false false

/-- Variant with the complemented inner `and` operands commuted. -/
public def andOrNotCommutedAnd : Pattern OpCode := andOrNotAndPattern true false

public theorem andOrNotCommutedAnd_valid : Pattern.Valid andOrNotCommutedAnd :=
  andOrNotAndPattern_valid true false

public def andOrNotAndConstantLeft : Pattern OpCode := andOrNotAndPattern false true
public theorem andOrNotAndConstantLeft_valid : Pattern.Valid andOrNotAndConstantLeft :=
  andOrNotAndPattern_valid false true

public def andOrNotCommutedAndConstantLeft : Pattern OpCode :=
  andOrNotAndPattern true true
public theorem andOrNotCommutedAndConstantLeft_valid :
    Pattern.Valid andOrNotCommutedAndConstantLeft :=
  andOrNotAndPattern_valid true true

end Veir.Passes.InstCombineLLVM.AndOrNotAnd

#print axioms Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotAnd_valid
#print axioms Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotCommutedAnd_valid
#print axioms Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotAndConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.AndOrNotAnd.andOrNotCommutedAndConstantLeft_valid
