module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.CountBitReverse

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

private def ctlzBitReverseFalsePattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let reversed ← MatchProg.operation (.llvm .intr__bitreverse) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__ctlz) #[reversed.res[0]!] #[ty]
        (fun props => props.is_zero_poison = false)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__cttz) { is_zero_poison := false }
      CreateProg.operation (.llvm .intr__cttz) #[x] #[ty] props)
    (fun result => result.res[0]!)

private def cttzBitReverseFalsePattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let reversed ← MatchProg.operation (.llvm .intr__bitreverse) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__cttz) #[reversed.res[0]!] #[ty]
        (fun props => props.is_zero_poison = false)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__ctlz) { is_zero_poison := false }
      CreateProg.operation (.llvm .intr__ctlz) #[x] #[ty] props)
    (fun result => result.res[0]!)

private def ctlzBitReverseTruePattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let reversed ← MatchProg.operation (.llvm .intr__bitreverse) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__ctlz) #[reversed.res[0]!] #[ty]
        (fun props => props.is_zero_poison = true)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__cttz) { is_zero_poison := true }
      CreateProg.operation (.llvm .intr__cttz) #[x] #[ty] props)
    (fun result => result.res[0]!)

private def cttzBitReverseTruePattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let reversed ← MatchProg.operation (.llvm .intr__bitreverse) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__cttz) #[reversed.res[0]!] #[ty]
        (fun props => props.is_zero_poison = true)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__ctlz) { is_zero_poison := true }
      CreateProg.operation (.llvm .intr__ctlz) #[x] #[ty] props)
    (fun result => result.res[0]!)

/-- Scalar `ctlz(bitreverse(x), z) -> cttz(x, z)` from InstCombineCalls.cpp:478. -/
public def ctlzBitReverse : Pattern OpCode :=
  ctlzBitReverseFalsePattern

/-- Scalar `cttz(bitreverse(x), z) -> ctlz(x, z)` from InstCombineCalls.cpp:478. -/
public def cttzBitReverse : Pattern OpCode :=
  cttzBitReverseFalsePattern

public def ctlzBitReverseZeroPoison : Pattern OpCode := ctlzBitReverseTruePattern
public def cttzBitReverseZeroPoison : Pattern OpCode := cttzBitReverseTruePattern

public theorem ctlzBitReverse_valid : Pattern.Valid ctlzBitReverse := by
  simp only [ctlzBitReverse, ctlzBitReverseFalsePattern]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ reversed hReversed
  obtain rfl := (bitreverse_iff w x reversed).mp hReversed
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = false := hFlag
  obtain rfl := (ctlz_iff w props _ source).mp hSource
  rw [hFlag']
  refine ⟨.int w (LLVM.Int.cttz x false),
    (cttz_iff w { is_zero_poison := false } x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, ctlz_bitreverse] using
    (isRefinedBy_refl (LLVM.Int.cttz x false))

public theorem cttzBitReverse_valid : Pattern.Valid cttzBitReverse := by
  simp only [cttzBitReverse, cttzBitReverseFalsePattern]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ reversed hReversed
  obtain rfl := (bitreverse_iff w x reversed).mp hReversed
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = false := hFlag
  obtain rfl := (cttz_iff w props _ source).mp hSource
  rw [hFlag']
  refine ⟨.int w (LLVM.Int.ctlz x false),
    (ctlz_iff w { is_zero_poison := false } x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, cttz_bitreverse] using
    (isRefinedBy_refl (LLVM.Int.ctlz x false))

public theorem ctlzBitReverseZeroPoison_valid : Pattern.Valid ctlzBitReverseZeroPoison := by
  simp only [ctlzBitReverseZeroPoison, ctlzBitReverseTruePattern]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ reversed hReversed
  obtain rfl := (bitreverse_iff w x reversed).mp hReversed
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = true := of_decide_eq_true hFlag
  obtain rfl := (ctlz_iff w props _ source).mp hSource
  rw [hFlag']
  refine ⟨.int w (LLVM.Int.cttz x true),
    (cttz_iff w { is_zero_poison := true } x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, ctlz_bitreverse] using
    (isRefinedBy_refl (LLVM.Int.cttz x true))

public theorem cttzBitReverseZeroPoison_valid : Pattern.Valid cttzBitReverseZeroPoison := by
  simp only [cttzBitReverseZeroPoison, cttzBitReverseTruePattern]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ reversed hReversed
  obtain rfl := (bitreverse_iff w x reversed).mp hReversed
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = true := of_decide_eq_true hFlag
  obtain rfl := (cttz_iff w props _ source).mp hSource
  rw [hFlag']
  refine ⟨.int w (LLVM.Int.ctlz x true),
    (ctlz_iff w { is_zero_poison := true } x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, cttz_bitreverse] using
    (isRefinedBy_refl (LLVM.Int.ctlz x true))

end Veir.Passes.InstCombineLLVM.CountBitReverse

#print axioms Veir.Passes.InstCombineLLVM.CountBitReverse.ctlzBitReverse_valid
#print axioms Veir.Passes.InstCombineLLVM.CountBitReverse.cttzBitReverse_valid
#print axioms Veir.Passes.InstCombineLLVM.CountBitReverse.ctlzBitReverseZeroPoison_valid
#print axioms Veir.Passes.InstCombineLLVM.CountBitReverse.cttzBitReverseZeroPoison_valid
