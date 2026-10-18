module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.I1MinMaxAnd

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

private def minMaxToAnd (opcode : OpCode) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let _ ← MatchProg.root opcode #[x, y] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let props ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[x, y] #[ty] props)
    (fun result => result.res[0]!)

/-- Scalar i1 specialization of InstCombineCalls.cpp:2353-2358: `umin` is `and`. -/
public def uminI1ToAnd : Pattern OpCode := minMaxToAnd (.llvm .intr__umin)

/-- Scalar i1 specialization of InstCombineCalls.cpp:2353-2358: `smax` is `and`. -/
public def smaxI1ToAnd : Pattern OpCode := minMaxToAnd (.llvm .intr__smax)

public theorem uminI1ToAnd_valid : Pattern.Valid uminI1ToAnd := by
  simp only [uminI1ToAnd, minMaxToAnd]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro type ⟨w, signedness⟩ hType hWidth
  subst type
  change w = 1 at hWidth
  subst w
  rintro x hX y hY
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType.mp hY
  rintro sourceProps source hSource
  rcases sourceProps with ⟨⟩
  obtain rfl := (umin_iff _ _ _ _).mp hSource
  refine ⟨.int 1 (LLVM.Int.and x y), (and_iff _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1, (LLVM.Int.umin x y).cast h ⊒ LLVM.Int.and x y
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, i1_umin_eq_and] using
    (isRefinedBy_refl (LLVM.Int.and x y))

public theorem smaxI1ToAnd_valid : Pattern.Valid smaxI1ToAnd := by
  simp only [smaxI1ToAnd, minMaxToAnd]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro type ⟨w, signedness⟩ hType hWidth
  subst type
  change w = 1 at hWidth
  subst w
  rintro x hX y hY
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType.mp hY
  rintro sourceProps source hSource
  rcases sourceProps with ⟨⟩
  obtain rfl := (smax_iff _ _ _ _).mp hSource
  refine ⟨.int 1 (LLVM.Int.and x y), (and_iff _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1, (LLVM.Int.smax x y).cast h ⊒ LLVM.Int.and x y
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, i1_smax_eq_and] using
    (isRefinedBy_refl (LLVM.Int.and x y))

end Veir.Passes.InstCombineLLVM.I1MinMaxAnd
