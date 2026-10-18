module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubI1

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

/-- Scalar specialization of InstCombineAddSub.cpp:2528-2530: i1 subtraction is xor. -/
public def subI1ToXor : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .sub) #[x, y] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let props ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[x, y] #[ty] props)
    (fun result => result.res[0]!)

public theorem subI1ToXor_valid : Pattern.Valid subI1ToXor := by
  simp only [subI1ToXor]
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
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  refine ⟨.int 1 (LLVM.Int.xor x y), (xor_iff _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1, (LLVM.Int.sub x y subProps.nsw subProps.nuw).cast h ⊒
    LLVM.Int.xor x y
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (i1_sub_refines_xor x y subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.SubI1
