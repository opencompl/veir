module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertSub

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def invertSubPattern (innerNotLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if innerNotLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let difference ← MatchProg.operation (.llvm .sub) #[notX.res[0]!, b] #[ty]
        (fun _ => true)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, difference.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[difference.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, b))
    (fun (ty, x, b) => do
      let props ← CreateProg.property (.llvm .add) default
      CreateProg.operation (.llvm .add) #[x, b] #[ty] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertSubPattern_valid (innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertSubPattern innerNotLeft outerNotLeft) := by
  cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertSubPattern, matchIntConstantNormalized, Bool.false_eq_true,
      ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [properties_of, guard_eq_cond_punit,
        MatchProg.collectBindings, MatchProg.collectDeclBindings,
        MatchProg.rootResults?, HandleContext.forbid, HandleContext.forbidMany,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpScalarPropertyPuddleSemantics
    rintro ⟨w, signedness⟩ x b
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro subProps difference hDifference
      obtain rfl := (sub_iff _ _ _ _ _).mp hDifference
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.add x b), (add_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        not_sub_not_left_refines_add w x b subProps.nsw subProps.nuw

public def invertSub : Pattern OpCode := invertSubPattern false false
public theorem invertSub_valid : Pattern.Valid invertSub :=
  invertSubPattern_valid false false
public def invertSubInnerLeft : Pattern OpCode := invertSubPattern true false
public theorem invertSubInnerLeft_valid : Pattern.Valid invertSubInnerLeft :=
  invertSubPattern_valid true false
public def invertSubOuterLeft : Pattern OpCode := invertSubPattern false true
public theorem invertSubOuterLeft_valid : Pattern.Valid invertSubOuterLeft :=
  invertSubPattern_valid false true
public def invertSubBothLeft : Pattern OpCode := invertSubPattern true true
public theorem invertSubBothLeft_valid : Pattern.Valid invertSubBothLeft :=
  invertSubPattern_valid true true

end Veir.Passes.InstCombineLLVM.FreeInvertSub
