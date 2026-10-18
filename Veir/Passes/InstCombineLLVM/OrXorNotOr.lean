module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.OrXorNotOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def orXorNotOrPattern (orCommuted notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let different ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
      let either ← if orCommuted then
        MatchProg.operation (.llvm .or) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let notEither ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, either.res[0]!]
          #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[either.res[0]!, minusOne]
          #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .or) #[different.res[0]!, notEither.res[0]!]
        #[ty] (fun _ => true)
      return (ty, a, b, minusOne))
    (fun (ty, a, b, minusOne) => do
      let ap ← CreateProg.property (.llvm .and) ()
      let and ← CreateProg.operation (.llvm .and) #[a, b] #[ty] ap
      let xp ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[and.res[0]!, minusOne] #[ty] xp)
    (fun result => result.res[0]!)

private theorem orXorNotOrPattern_valid (orCommuted notConstantLeft : Bool) :
    Pattern.Valid (orXorNotOrPattern orCommuted notConstantLeft) := by
  cases orCommuted <;> cases notConstantLeft <;>
    simp only [orXorNotOrPattern, matchIntConstantNormalized,
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
      rintro ⟨⟩ different hDifferent
      obtain rfl := (xor_iff _ _ _ _).mp hDifferent
      rintro innerProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ notEither hNotEither
      obtain rfl := (xor_iff _ _ _ _).mp hNotEither
      rintro outerProps source hSource
      obtain rfl := (or_iff _ _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.and a b), (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor (LLVM.Int.and a b) (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (xor_or_not_or_refines_not_and w a b
          innerProps.disjoint outerProps.disjoint)

/- Scalar semantic specialization of InstCombineAndOrXor.cpp:1988-1991.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def orXorNotOr : Pattern OpCode := orXorNotOrPattern false false

public theorem orXorNotOr_valid : Pattern.Valid orXorNotOr :=
  orXorNotOrPattern_valid false false

public def orXorNotCommutedOr : Pattern OpCode := orXorNotOrPattern true false

public theorem orXorNotCommutedOr_valid : Pattern.Valid orXorNotCommutedOr :=
  orXorNotOrPattern_valid true false

public def orXorNotOrConstantLeft : Pattern OpCode := orXorNotOrPattern false true
public theorem orXorNotOrConstantLeft_valid : Pattern.Valid orXorNotOrConstantLeft :=
  orXorNotOrPattern_valid false true

public def orXorNotCommutedOrConstantLeft : Pattern OpCode :=
  orXorNotOrPattern true true
public theorem orXorNotCommutedOrConstantLeft_valid :
    Pattern.Valid orXorNotCommutedOrConstantLeft :=
  orXorNotOrPattern_valid true true

end Veir.Passes.InstCombineLLVM.OrXorNotOr

#print axioms Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotOr_valid
#print axioms Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotCommutedOr_valid
#print axioms Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotOrConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.OrXorNotOr.orXorNotCommutedOrConstantLeft_valid
