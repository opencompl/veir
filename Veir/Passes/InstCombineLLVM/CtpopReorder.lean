module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.CtpopReorder

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

/-- Scalar bitreverse arm of InstCombineCalls.cpp:659-665. -/
public def ctpopBitReverse : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let reversed ← MatchProg.operation (.llvm .intr__bitreverse) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__ctpop) #[reversed.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__ctpop) ()
      CreateProg.operation (.llvm .intr__ctpop) #[x] #[ty] props)
    (fun result => result.res[0]!)

public theorem ctpopBitReverse_valid : Pattern.Valid ctpopBitReverse := by
  simp only [ctpopBitReverse]
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
  rintro _ source hSource
  obtain rfl := (ctpop_iff w _ source).mp hSource
  refine ⟨.int w (LLVM.Int.ctpop x), (ctpop_iff w x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, ctpop_bitreverse] using
    (isRefinedBy_refl (LLVM.Int.ctpop x))

/-- Scalar byte-swap arm of InstCombineCalls.cpp:659-665. -/
public def ctpopBSwap : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let swapped ← MatchProg.operation (.llvm .intr__bswap) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__ctpop) #[swapped.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__ctpop) ()
      CreateProg.operation (.llvm .intr__ctpop) #[x] #[ty] props)
    (fun result => result.res[0]!)

public theorem ctpopBSwap_valid : Pattern.Valid ctpopBSwap := by
  simp only [ctpopBSwap]
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
  rintro _ swapped hSwapped
  obtain rfl := (bswap_iff w x swapped).mp hSwapped
  rintro _ source hSource
  obtain rfl := (ctpop_iff w _ source).mp hSource
  refine ⟨.int w (LLVM.Int.ctpop x), (ctpop_iff w x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, ctpop_bswap] using
    (isRefinedBy_refl (LLVM.Int.ctpop x))

private def ctpopFunnelShift (opcode : Llvm) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let amount ← MatchProg.value ty
      let rotated ← MatchProg.operation (.llvm opcode) #[x, x, amount] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .intr__ctpop) #[rotated.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .intr__ctpop) ()
      CreateProg.operation (.llvm .intr__ctpop) #[x] #[ty] props)
    (fun result => result.res[0]!)

/-- Scalar `fshl(x, x, amount)` rotate arm of InstCombineCalls.cpp:663-665. -/
public def ctpopFShl : Pattern OpCode := ctpopFunnelShift Llvm.intr__fshl

public theorem ctpopFShl_valid : Pattern.Valid ctpopFShl := by
  simp only [ctpopFShl, ctpopFunnelShift]
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
  rintro amount hAmount
  obtain ⟨amount, rfl⟩ := RuntimeValue.Conforms.integerType.mp hAmount
  rintro _ rotated hRotated
  obtain rfl := (fshl_iff w x x amount rotated).mp hRotated
  rintro _ source hSource
  obtain rfl := (ctpop_iff w _ source).mp hSource
  refine ⟨.int w (LLVM.Int.ctpop x), (ctpop_iff w x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using ctpop_fshl_self x amount

/-- Scalar `fshr(x, x, amount)` rotate arm of InstCombineCalls.cpp:663-665. -/
public def ctpopFShr : Pattern OpCode := ctpopFunnelShift Llvm.intr__fshr

public theorem ctpopFShr_valid : Pattern.Valid ctpopFShr := by
  simp only [ctpopFShr, ctpopFunnelShift]
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
  rintro amount hAmount
  obtain ⟨amount, rfl⟩ := RuntimeValue.Conforms.integerType.mp hAmount
  rintro _ rotated hRotated
  obtain rfl := (fshr_iff w x x amount rotated).mp hRotated
  rintro _ source hSource
  obtain rfl := (ctpop_iff w _ source).mp hSource
  refine ⟨.int w (LLVM.Int.ctpop x), (ctpop_iff w x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using ctpop_fshr_self x amount

end Veir.Passes.InstCombineLLVM.CtpopReorder

#print axioms Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopBitReverse_valid
#print axioms Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopBSwap_valid
#print axioms Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopFShl_valid
#print axioms Veir.Passes.InstCombineLLVM.CtpopReorder.ctpopFShr_valid
