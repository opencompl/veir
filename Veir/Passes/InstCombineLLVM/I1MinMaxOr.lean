module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.I1MinMaxOr

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

private def minMaxToOr (opcode : OpCode) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let _ ← MatchProg.root opcode #[x, y] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let props ← CreateProg.property (.llvm .or) { disjoint := false }
      CreateProg.operation (.llvm .or) #[x, y] #[ty] props)
    (fun result => result.res[0]!)

/-- Scalar i1 specialization of InstCombineCalls.cpp:2360-2365: `umax` is `or`. -/
public def umaxI1ToOr : Pattern OpCode := minMaxToOr (.llvm .intr__umax)

/-- Scalar i1 specialization of InstCombineCalls.cpp:2360-2365: `smin` is `or`. -/
public def sminI1ToOr : Pattern OpCode := minMaxToOr (.llvm .intr__smin)

public theorem umaxI1ToOr_valid : Pattern.Valid umaxI1ToOr := by
  simp only [umaxI1ToOr, minMaxToOr]
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
  obtain rfl := (umax_iff _ _ _ _).mp hSource
  refine ⟨.int 1 (LLVM.Int.or x y), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1, (LLVM.Int.umax x y).cast h ⊒ LLVM.Int.or x y
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, i1_umax_eq_or] using
    (isRefinedBy_refl (LLVM.Int.or x y))

public theorem sminI1ToOr_valid : Pattern.Valid sminI1ToOr := by
  simp only [sminI1ToOr, minMaxToOr]
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
  obtain rfl := (smin_iff _ _ _ _).mp hSource
  refine ⟨.int 1 (LLVM.Int.or x y), (or_iff _ _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1, (LLVM.Int.smin x y).cast h ⊒ LLVM.Int.or x y
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, i1_smin_eq_or] using
    (isRefinedBy_refl (LLVM.Int.or x y))

end Veir.Passes.InstCombineLLVM.I1MinMaxOr
