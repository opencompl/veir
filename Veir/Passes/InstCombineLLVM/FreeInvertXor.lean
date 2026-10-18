module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertXor

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def invertXorPattern
    (invertLeft innerNotLeft outerNotLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let other ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let notX ← if innerNotLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let both ← if invertLeft then
        MatchProg.operation (.llvm .xor) #[notX.res[0]!, other] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[other, notX.res[0]!] #[ty] (fun _ => true)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, both.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[both.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, other))
    (fun (ty, x, other) => do
      let props ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[x, other] #[ty] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertXorPattern_valid
    (invertLeft innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertXorPattern invertLeft innerNotLeft outerNotLeft) := by
  cases invertLeft <;> cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertXorPattern, matchIntConstantNormalized, Bool.false_eq_true,
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
    rintro ⟨w, signedness⟩ x other
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ notX hNotX
      obtain rfl := (xor_iff _ _ _ _).mp hNotX
      rintro ⟨⟩ both hBoth
      obtain rfl := (xor_iff _ _ _ _).mp hBoth
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor x other), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using
        not_xor_not_right_refines_xor w other x

public def invertXorRight : Pattern OpCode := invertXorPattern false false false
public theorem invertXorRight_valid : Pattern.Valid invertXorRight :=
  invertXorPattern_valid false false false
public def invertXorRightInnerLeft : Pattern OpCode := invertXorPattern false true false
public theorem invertXorRightInnerLeft_valid : Pattern.Valid invertXorRightInnerLeft :=
  invertXorPattern_valid false true false
public def invertXorRightOuterLeft : Pattern OpCode := invertXorPattern false false true
public theorem invertXorRightOuterLeft_valid : Pattern.Valid invertXorRightOuterLeft :=
  invertXorPattern_valid false false true
public def invertXorRightBothLeft : Pattern OpCode := invertXorPattern false true true
public theorem invertXorRightBothLeft_valid : Pattern.Valid invertXorRightBothLeft :=
  invertXorPattern_valid false true true

public def invertXorLeft : Pattern OpCode := invertXorPattern true false false
public theorem invertXorLeft_valid : Pattern.Valid invertXorLeft :=
  invertXorPattern_valid true false false
public def invertXorLeftInnerLeft : Pattern OpCode := invertXorPattern true true false
public theorem invertXorLeftInnerLeft_valid : Pattern.Valid invertXorLeftInnerLeft :=
  invertXorPattern_valid true true false
public def invertXorLeftOuterLeft : Pattern OpCode := invertXorPattern true false true
public theorem invertXorLeftOuterLeft_valid : Pattern.Valid invertXorLeftOuterLeft :=
  invertXorPattern_valid true false true
public def invertXorLeftBothLeft : Pattern OpCode := invertXorPattern true true true
public theorem invertXorLeftBothLeft_valid : Pattern.Valid invertXorLeftBothLeft :=
  invertXorPattern_valid true true true

end Veir.Passes.InstCombineLLVM.FreeInvertXor
