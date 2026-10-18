module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertAdd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def invertAddPattern
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
      let sum ← if invertLeft then
        MatchProg.operation (.llvm .add) #[notX.res[0]!, other] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .add) #[other, notX.res[0]!] #[ty] (fun _ => true)
      let _ ← if outerNotLeft then
        MatchProg.root (.llvm .xor) #[minusOne, sum.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[sum.res[0]!, minusOne] #[ty] (fun _ => true)
      return (ty, x, other))
    (fun (ty, x, other) => do
      let props ← CreateProg.property (.llvm .sub) default
      CreateProg.operation (.llvm .sub) #[x, other] #[ty] props)
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem invertAddPattern_valid
    (invertLeft innerNotLeft outerNotLeft : Bool) :
    Pattern.Valid (invertAddPattern invertLeft innerNotLeft outerNotLeft) := by
  cases invertLeft <;> cases innerNotLeft <;> cases outerNotLeft <;>
    simp only [invertAddPattern, matchIntConstantNormalized, Bool.false_eq_true,
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
      rintro addProps sum hSum
      obtain rfl := (add_iff _ _ _ _ _).mp hSum
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.sub x other), (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm, llvm_add_comm_flags] using
        not_add_not_right_refines_sub w other x addProps.nsw addProps.nuw

public def invertAddRight : Pattern OpCode := invertAddPattern false false false
public theorem invertAddRight_valid : Pattern.Valid invertAddRight :=
  invertAddPattern_valid false false false
public def invertAddRightInnerLeft : Pattern OpCode := invertAddPattern false true false
public theorem invertAddRightInnerLeft_valid : Pattern.Valid invertAddRightInnerLeft :=
  invertAddPattern_valid false true false
public def invertAddRightOuterLeft : Pattern OpCode := invertAddPattern false false true
public theorem invertAddRightOuterLeft_valid : Pattern.Valid invertAddRightOuterLeft :=
  invertAddPattern_valid false false true
public def invertAddRightBothLeft : Pattern OpCode := invertAddPattern false true true
public theorem invertAddRightBothLeft_valid : Pattern.Valid invertAddRightBothLeft :=
  invertAddPattern_valid false true true

public def invertAddLeft : Pattern OpCode := invertAddPattern true false false
public theorem invertAddLeft_valid : Pattern.Valid invertAddLeft :=
  invertAddPattern_valid true false false
public def invertAddLeftInnerLeft : Pattern OpCode := invertAddPattern true true false
public theorem invertAddLeftInnerLeft_valid : Pattern.Valid invertAddLeftInnerLeft :=
  invertAddPattern_valid true true false
public def invertAddLeftOuterLeft : Pattern OpCode := invertAddPattern true false true
public theorem invertAddLeftOuterLeft_valid : Pattern.Valid invertAddLeftOuterLeft :=
  invertAddPattern_valid true false true
public def invertAddLeftBothLeft : Pattern OpCode := invertAddPattern true true true
public theorem invertAddLeftBothLeft_valid : Pattern.Valid invertAddLeftBothLeft :=
  invertAddPattern_valid true true true

end Veir.Passes.InstCombineLLVM.FreeInvertAdd
