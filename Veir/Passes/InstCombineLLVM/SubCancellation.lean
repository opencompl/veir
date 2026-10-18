module
public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.SubCancellation
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t
private def zeroConstantProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

/-- Scalar specialization of InstCombineAddSub.cpp:2718-2721: `X-(X+Y) -> -Y`. -/
public def subAddSelf : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let sum ← MatchProg.operation (.llvm .add) #[x, y] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[x, sum.res[0]!] #[ty] (fun _ => true)
    return (ty, y))
  (fun (ty, y) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty zeroConstantProperty
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    let sp ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[zero.res[0]!, y] #[ty] sp)
  (fun result => result.res[0]!)

public theorem subAddSelf_valid : Pattern.Valid subAddSelf := by
  simp only [subAddSelf]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x y
  rintro addProps sum hSum
  obtain rfl := (add_iff _ _ _ _ _).mp hSum
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  simp [zeroConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
      (ofInt_normalizeValue { bitwidth := w, signedness := s } 0).symm
  refine ⟨.int w (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y),
    (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_add_self_flags_refine_neg w x y addProps.nsw addProps.nuw subProps.nsw subProps.nuw)

/-- Commuted add form of InstCombineAddSub.cpp:2718-2721: `X-(Y+X) -> -Y`. -/
public def subAddSelfCommuted : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let sum ← MatchProg.operation (.llvm .add) #[y, x] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[x, sum.res[0]!] #[ty] (fun _ => true)
    return (ty, y))
  (fun (ty, y) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty zeroConstantProperty
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    let sp ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[zero.res[0]!, y] #[ty] sp)
  (fun result => result.res[0]!)

public theorem subAddSelfCommuted_valid : Pattern.Valid subAddSelfCommuted := by
  simp only [subAddSelfCommuted]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x y
  rintro addProps sum hSum
  obtain rfl := (add_iff _ _ _ _ _).mp hSum
  rintro subProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  simp [zeroConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
      (ofInt_normalizeValue { bitwidth := w, signedness := s } 0).symm
  refine ⟨.int w (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y),
    (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_add_self_commuted_flags_refine_neg w x y addProps.nsw addProps.nuw
      subProps.nsw subProps.nuw)

/-- Scalar specialization of InstCombineAddSub.cpp:2723-2725: `(X-Y)-X -> -Y`. -/
public def subSelfFromSub : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let difference ← MatchProg.operation (.llvm .sub) #[x, y] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .sub) #[difference.res[0]!, x] #[ty] (fun _ => true)
    return (ty, y))
  (fun (ty, y) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty zeroConstantProperty
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    let sp ← CreateProg.property (.llvm .sub) default
    CreateProg.operation (.llvm .sub) #[zero.res[0]!, y] #[ty] sp)
  (fun result => result.res[0]!)

public theorem subSelfFromSub_valid : Pattern.Valid subSelfFromSub := by
  simp only [subSelfFromSub]; unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
      HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
      HandleContext.insertFresh, HandleContext.insertManyFresh, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ x y
  rintro innerProps difference hDifference
  obtain rfl := (sub_iff _ _ _ _ _).mp hDifference
  rintro outerProps source hSource
  obtain rfl := (sub_iff _ _ _ _ _).mp hSource
  simp [zeroConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
      (ofInt_normalizeValue { bitwidth := w, signedness := s } 0).symm
  refine ⟨.int w (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y),
    (sub_iff _ _ _ _ _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (sub_self_from_sub_flags_refine_neg w x y innerProps.nsw innerProps.nuw
      outerProps.nsw outerProps.nuw)
end Veir.Passes.InstCombineLLVM.SubCancellation
