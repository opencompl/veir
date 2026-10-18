module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
public import Veir.Passes.InstCombineLLVM.ProofTactics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorNotMixed

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def xorOrNotAndPattern (andCommuted notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let either ← MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let both ← if andCommuted then
        MatchProg.operation (.llvm .and) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
      let notBoth ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, both.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[both.res[0]!, minusOne] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .xor) #[either.res[0]!, notBoth.res[0]!]
        #[ty] (fun _ => true)
      return (ty, a, b, minusOne))
    (fun (ty, a, b, minusOne) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      let xor ← CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp
      let np ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[xor.res[0]!, minusOne] #[ty] np)
    (fun result => result.res[0]!)

set_option maxHeartbeats 800000 in
private theorem xorOrNotAndPattern_valid (andCommuted notConstantLeft : Bool) :
    Pattern.Valid (xorOrNotAndPattern andCommuted notConstantLeft) := by
  cases andCommuted <;> cases notConstantLeft <;> simp only [xorOrNotAndPattern, matchIntConstantNormalized,
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
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro ⟨⟩ notBoth hNotBoth
      obtain rfl := (xor_iff _ _ _ _).mp hNotBoth
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
        (or_xor_not_and_refines_not_xor w a b orProps.disjoint)

private def xorAndNotOrPattern (orCommuted notConstantLeft : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let minusOne ← matchIntConstantNormalized ty (-1)
      let both ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
      let either ← if orCommuted then
        MatchProg.operation (.llvm .or) #[b, a] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[a, b] #[ty] (fun _ => true)
      let notEither ← if notConstantLeft then
        MatchProg.operation (.llvm .xor) #[minusOne, either.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .xor) #[either.res[0]!, minusOne] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .xor) #[both.res[0]!, notEither.res[0]!]
        #[ty] (fun _ => true)
      return (ty, a, b, minusOne))
    (fun (ty, a, b, minusOne) => do
      let xp ← CreateProg.property (.llvm .xor) ()
      let xor ← CreateProg.operation (.llvm .xor) #[a, b] #[ty] xp
      let np ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[xor.res[0]!, minusOne] #[ty] np)
    (fun result => result.res[0]!)

set_option maxHeartbeats 800000 in
private theorem xorAndNotOrPattern_valid (orCommuted notConstantLeft : Bool) :
    Pattern.Valid (xorAndNotOrPattern orCommuted notConstantLeft) := by
  cases orCommuted <;> cases notConstantLeft <;> simp only [xorAndNotOrPattern, matchIntConstantNormalized,
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
      rintro ⟨⟩ both hBoth
      obtain rfl := (and_iff _ _ _ _).mp hBoth
      rintro orProps either hEither
      obtain rfl := (or_iff _ _ _ _ _).mp hEither
      rintro ⟨⟩ notEither hNotEither
      obtain rfl := (xor_iff _ _ _ _).mp hNotEither
      rintro ⟨⟩ source hSource
      obtain rfl := (xor_iff _ _ _ _).mp hSource
      rintro hMinusOne
      have hMinusOneBits : BitVec.ofInt w minusOneAttr.value = BitVec.ofInt w (-1) := by
        simpa [isNormalizedIntConstant, asLLVMConstantProperties,
          IsTypeAttr.cast?_of] using hMinusOne
      rw [hMinusOneBits]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor (LLVM.Int.xor a b) (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (and_xor_not_or_refines_not_xor w a b orProps.disjoint)

/- Scalar semantic specialization of InstCombineAndOrXor.cpp:4859-4863.
   Puddle currently omits the source's profitability-only one-use guard. -/
public def xorOrNotAnd : Pattern OpCode := xorOrNotAndPattern false false
public theorem xorOrNotAnd_valid : Pattern.Valid xorOrNotAnd :=
  xorOrNotAndPattern_valid false false

public def xorOrNotCommutedAnd : Pattern OpCode := xorOrNotAndPattern true false
public theorem xorOrNotCommutedAnd_valid : Pattern.Valid xorOrNotCommutedAnd :=
  xorOrNotAndPattern_valid true false

public def xorAndNotOr : Pattern OpCode := xorAndNotOrPattern false false
public theorem xorAndNotOr_valid : Pattern.Valid xorAndNotOr :=
  xorAndNotOrPattern_valid false false

public def xorAndNotCommutedOr : Pattern OpCode := xorAndNotOrPattern true false
public theorem xorAndNotCommutedOr_valid : Pattern.Valid xorAndNotCommutedOr :=
  xorAndNotOrPattern_valid true false


public def xorOrNotAndConstantLeft : Pattern OpCode := xorOrNotAndPattern false true
public theorem xorOrNotAndConstantLeft_valid : Pattern.Valid xorOrNotAndConstantLeft :=
  xorOrNotAndPattern_valid false true

public def xorOrNotCommutedAndConstantLeft : Pattern OpCode := xorOrNotAndPattern true true
public theorem xorOrNotCommutedAndConstantLeft_valid :
    Pattern.Valid xorOrNotCommutedAndConstantLeft :=
  xorOrNotAndPattern_valid true true

public def xorAndNotOrConstantLeft : Pattern OpCode := xorAndNotOrPattern false true
public theorem xorAndNotOrConstantLeft_valid : Pattern.Valid xorAndNotOrConstantLeft :=
  xorAndNotOrPattern_valid false true

public def xorAndNotCommutedOrConstantLeft : Pattern OpCode := xorAndNotOrPattern true true
public theorem xorAndNotCommutedOrConstantLeft_valid :
    Pattern.Valid xorAndNotCommutedOrConstantLeft :=
  xorAndNotOrPattern_valid true true

end Veir.Passes.InstCombineLLVM.XorNotMixed

#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotAnd_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotCommutedAnd_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotOr_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotCommutedOr_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotAndConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorOrNotCommutedAndConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotOrConstantLeft_valid
#print axioms Veir.Passes.InstCombineLLVM.XorNotMixed.xorAndNotCommutedOrConstantLeft_valid
