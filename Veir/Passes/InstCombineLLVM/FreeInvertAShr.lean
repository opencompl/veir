module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertAShr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def invertAShrPattern (innerNotLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let amount ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if innerNotLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let shifted ← MatchProg.operation (.llvm .ashr) #[notX.res[0]!, amount] #[ty]
        (fun _ => true)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, shifted.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[shifted.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, amount))
    (fun (ty, x, amount) => do
      let props ← CreateProg.property (.llvm .ashr) default
      CreateProg.operation (.llvm .ashr) #[x, amount] #[ty] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertAShrPattern_valid (innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertAShrPattern innerNotLeft outerNotLeft) := by
  cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertAShrPattern, matchIntConstantNormalized, Bool.false_eq_true,
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
    rintro ⟨w, signedness⟩ x amount
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro shiftProps shifted hShifted
      obtain rfl := (ashr_iff _ _ _ _ _).mp hShifted
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.ashr x amount false), (ashr_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        not_ashr_not_refines_ashr w x amount shiftProps.exact

public def invertAShr : Pattern OpCode := invertAShrPattern false false
public theorem invertAShr_valid : Pattern.Valid invertAShr :=
  invertAShrPattern_valid false false
public def invertAShrInnerLeft : Pattern OpCode := invertAShrPattern true false
public theorem invertAShrInnerLeft_valid : Pattern.Valid invertAShrInnerLeft :=
  invertAShrPattern_valid true false
public def invertAShrOuterLeft : Pattern OpCode := invertAShrPattern false true
public theorem invertAShrOuterLeft_valid : Pattern.Valid invertAShrOuterLeft :=
  invertAShrPattern_valid false true
public def invertAShrBothLeft : Pattern OpCode := invertAShrPattern true true
public theorem invertAShrBothLeft_valid : Pattern.Valid invertAShrBothLeft :=
  invertAShrPattern_valid true true

end Veir.Passes.InstCombineLLVM.FreeInvertAShr
