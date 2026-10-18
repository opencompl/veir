module

public import Veir.Passes.InstCombineLLVM.CoreInversionSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def doubleNotPattern (innerLeft outerLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let inner ← if innerLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[x, minusOne] #[ty] (fun _ => true)
      let _ ← if outerLeft then
        MatchProg.root (.llvm .xor) #[minusOne, inner.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[inner.res[0]!, minusOne] #[ty] (fun _ => true)
      return x)
    pure
    (fun x => x)

private theorem doubleNotPattern_valid (innerLeft outerLeft : Bool) :
    Pattern.Valid (doubleNotPattern innerLeft outerLeft) := by
  cases innerLeft <;> cases outerLeft <;>
    simp only [doubleNotPattern, matchIntConstantNormalized, Bool.false_eq_true,
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
    rintro ⟨w, signedness⟩ x
    rintro ⟨constantValue⟩ minusOne hInterpMinusOne
    cases constantValue with
    | float _ | dense _ | string _ =>
      rintro _ _ _ _ _ _ hMinusOne
      simp [isNormalizedIntConstant, asLLVMConstantProperties] at hMinusOne
    | integer minusOneAttr =>
      obtain rfl := (constant_iff _ minusOneAttr _).mp hInterpMinusOne
      rintro ⟨⟩ inner hInner
      obtain rfl := (xor_iff _ _ _ _).mp hInner
      rintro ⟨⟩ source hSource hMinusOne
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_xor_comm] using double_not_refines w x

public def doubleNot : Pattern OpCode := doubleNotPattern false false
public theorem doubleNot_valid : Pattern.Valid doubleNot :=
  doubleNotPattern_valid false false

public def doubleNotInnerLeft : Pattern OpCode := doubleNotPattern true false
public theorem doubleNotInnerLeft_valid : Pattern.Valid doubleNotInnerLeft :=
  doubleNotPattern_valid true false

public def doubleNotOuterLeft : Pattern OpCode := doubleNotPattern false true
public theorem doubleNotOuterLeft_valid : Pattern.Valid doubleNotOuterLeft :=
  doubleNotPattern_valid false true

public def doubleNotBothLeft : Pattern OpCode := doubleNotPattern true true
public theorem doubleNotBothLeft_valid : Pattern.Valid doubleNotBothLeft :=
  doubleNotPattern_valid true true

end Veir.Passes.InstCombineLLVM.FreeInvertDoubleNot
