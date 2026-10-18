module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SubAndNot

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def allOnesProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-1) intType))

/-- Scalar semantic generalization of InstCombineAddSub.cpp:2874-2878:
    `X - (X and Y) -> X and (Y xor -1)`. LLVM's one-use/constant guard is a
    profitability condition; the Puddle rule proves the identity for every scalar integer input. -/
public def subAndNot : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let and ← MatchProg.operation (.llvm .and) #[x, y] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[x, and.res[0]!] #[ty] (fun _ => true)
    return (ty, x, y))
  (fun (ty, x, y) => do
    let cp ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
    let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne.res[0]!] #[ty] xp
    let ap ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[x, notY.res[0]!] #[ty] ap)
  (fun result => result.res[0]!)

public theorem subAndNot_valid : Pattern.Valid subAndNot := by
  simp only [subAndNot]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x y
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  simp [allOnesProperty, IsTypeAttr.cast?_of]
  refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
      (ofInt_normalizeValue { bitwidth := w, signedness := s } (-1)).symm
  refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
    (xor_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨.int w (LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
    (and_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_and_refines_and_not w x y subProps.nsw subProps.nuw)

/-- Variant with the matched inner `and` operands commuted. -/
public def subCommutedAndNot : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let and ← MatchProg.operation (.llvm .and) #[y, x] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[x, and.res[0]!] #[ty] (fun _ => true)
    return (ty, x, y))
  (fun (ty, x, y) => do
    let cp ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
    let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
    let xp ← CreateProg.property (.llvm .xor) ()
    let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne.res[0]!] #[ty] xp
    let ap ← CreateProg.property (.llvm .and) ()
    CreateProg.operation (.llvm .and) #[x, notY.res[0]!] #[ty] ap)
  (fun result => result.res[0]!)

public theorem subCommutedAndNot_valid : Pattern.Valid subCommutedAndNot := by
  simp only [subCommutedAndNot]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x y
  rintro ⟨⟩ and hAnd
  obtain rfl := (and_iff _ _ _ _).mp hAnd
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  simp [allOnesProperty, IsTypeAttr.cast?_of]
  refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
      (ofInt_normalizeValue { bitwidth := w, signedness := s } (-1)).symm
  refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
    (xor_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨.int w (LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
    (and_iff _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, llvm_and_comm] using
    (sub_and_refines_and_not w x y subProps.nsw subProps.nuw)

end Veir.Passes.InstCombineLLVM.SubAndNot
