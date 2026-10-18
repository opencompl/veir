module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NegateTrunc

open Veir
open Veir.Data
open Veir.Puddle
open Veir.Passes.InstCombineLLVM

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def zeroConstantProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

/-- General scalar algebraic form underlying InstCombineNegator.cpp:391-397:
    `-(trunc x) -> trunc(-x)`.  LLVM's recursive implementation may simplify the new
    wide negation further; this finite pattern materializes it directly. -/
public def negateTruncCommute : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let narrowTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value wideTy
      let truncated ← MatchProg.operation (.llvm .trunc) #[x] #[narrowTy]
        (fun _ => true)
      let narrowZero ← matchIntConstant narrowTy 0
      let _ ← MatchProg.root (.llvm .sub) #[narrowZero, truncated.res[0]!] #[narrowTy]
        (fun _ => true)
      return (wideTy, narrowTy, x))
    (fun (wideTy, narrowTy, x) => do
      let zeroProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        wideTy zeroConstantProperty
      let wideZero ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] zeroProps
      let subProps ← CreateProg.property (.llvm .sub) default
      let negated ← CreateProg.operation (.llvm .sub) #[wideZero.res[0]!, x] #[wideTy]
        subProps
      let truncProps ← CreateProg.property (.llvm .trunc) default
      CreateProg.operation (.llvm .trunc) #[negated.res[0]!] #[narrowTy] truncProps)
    (fun result => result.res[0]!)

public theorem negateTruncCommute_valid : Pattern.Valid negateTruncCommute := by
  simp only [negateTruncCommute, matchIntConstant]
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
  rintro ⟨wideW, wideSignedness⟩ ⟨narrowW, narrowSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro truncProps truncated hTruncated
  obtain ⟨hNarrow, rfl⟩ :=
    (trunc_iff wideW narrowW truncProps x truncated).mp hTruncated
  rintro ⟨narrowZeroValue⟩ narrowZero hNarrowZero hInterpNarrowZero
  cases narrowZeroValue with
  | float _ | dense _ | string _ => simp at hNarrowZero
  | integer narrowZeroAttr =>
    have hNarrowZeroValue : narrowZeroAttr.value = 0 :=
      of_decide_eq_true hNarrowZero
    obtain rfl := (constant_iff _ narrowZeroAttr _).mp hInterpNarrowZero
    rintro outerProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rw [hNarrowZeroValue]
    simp [zeroConstantProperty, IsTypeAttr.cast?_of]
    refine ⟨.int wideW (.val (BitVec.ofInt wideW 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg
        (fun z => RuntimeValue.int wideW (.val z))
        (ofInt_normalizeValue { bitwidth := wideW, signedness := wideSignedness } 0).symm
    refine ⟨.int wideW (LLVM.Int.sub (.val (BitVec.ofInt wideW 0)) x), ?_, ?_⟩
    · exact (sub_iff _ _ _ _ _).mpr rfl
    refine ⟨.int narrowW
      (LLVM.Int.trunc (LLVM.Int.sub (.val (BitVec.ofInt wideW 0)) x)
        narrowW false false hNarrow), ?_, ?_⟩
    · exact (trunc_iff wideW narrowW default _ _).mpr ⟨hNarrow, rfl⟩
    change ∃ h : narrowW = narrowW,
      (LLVM.Int.sub (.val (BitVec.ofInt narrowW 0))
        (LLVM.Int.trunc x narrowW truncProps.nsw truncProps.nuw hNarrow)
        outerProps.nsw outerProps.nuw).cast h ⊒
        LLVM.Int.trunc (LLVM.Int.sub (.val (BitVec.ofInt wideW 0)) x)
          narrowW false false hNarrow
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (neg_trunc_refines wideW narrowW hNarrow x
        truncProps.nsw truncProps.nuw outerProps.nsw outerProps.nuw)

/-- Concrete scalar specialization of InstCombineNegator.cpp:391-397 where the recursive
    negation of the truncation operand is discharged by double negation:
    `-(trunc(-x)) -> trunc(x)`.  The replacement truncation has no poison flags, matching
    `Builder.CreateTrunc`, and the recursive negation is requested with NSW disabled. -/
public def negateTruncDoubleNegation : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let narrowTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value wideTy
      let wideZero ← matchIntConstant wideTy 0
      let negated ← MatchProg.operation (.llvm .sub) #[wideZero, x] #[wideTy]
        (fun _ => true)
      let truncated ← MatchProg.operation (.llvm .trunc) #[negated.res[0]!] #[narrowTy]
        (fun _ => true)
      let narrowZero ← matchIntConstant narrowTy 0
      let _ ← MatchProg.root (.llvm .sub) #[narrowZero, truncated.res[0]!] #[narrowTy]
        (fun _ => true)
      return (narrowTy, x))
    (fun (narrowTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) default
      CreateProg.operation (.llvm .trunc) #[x] #[narrowTy] props)
    (fun result => result.res[0]!)

public theorem negateTruncDoubleNegation_valid :
    Pattern.Valid negateTruncDoubleNegation := by
  simp only [negateTruncDoubleNegation, matchIntConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.insertFreshBindings,
        CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨wideW, wideSignedness⟩ ⟨narrowW, narrowSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro ⟨wideZeroValue⟩ wideZero hWideZero hInterpWideZero
  cases wideZeroValue with
  | float _ | dense _ | string _ => simp at hWideZero
  | integer wideZeroAttr =>
    have hWideZeroValue : wideZeroAttr.value = 0 := of_decide_eq_true hWideZero
    obtain rfl := (constant_iff _ wideZeroAttr _).mp hInterpWideZero
    rintro innerProps negated hNegated
    obtain rfl := (sub_iff _ _ _ _ _).mp hNegated
    rintro truncProps truncated hTruncated
    obtain ⟨hNarrow, rfl⟩ :=
      (trunc_iff wideW narrowW truncProps _ truncated).mp hTruncated
    rintro ⟨narrowZeroValue⟩ narrowZero hNarrowZero hInterpNarrowZero
    cases narrowZeroValue with
    | float _ | dense _ | string _ => simp at hNarrowZero
    | integer narrowZeroAttr =>
      have hNarrowZeroValue : narrowZeroAttr.value = 0 :=
        of_decide_eq_true hNarrowZero
      obtain rfl := (constant_iff _ narrowZeroAttr _).mp hInterpNarrowZero
      rintro outerProps source hSource
      obtain rfl := (sub_iff _ _ _ _ _).mp hSource
      rw [hWideZeroValue, hNarrowZeroValue]
      refine ⟨.int narrowW (LLVM.Int.trunc x narrowW false false hNarrow), ?_, ?_⟩
      · exact (trunc_iff wideW narrowW default x _).mpr ⟨hNarrow, rfl⟩
      change ∃ h : narrowW = narrowW,
        (LLVM.Int.sub (.val (BitVec.ofInt narrowW 0))
          (LLVM.Int.trunc
            (LLVM.Int.sub (.val (BitVec.ofInt wideW 0)) x
              innerProps.nsw innerProps.nuw)
            narrowW truncProps.nsw truncProps.nuw hNarrow)
          outerProps.nsw outerProps.nuw).cast h ⊒
          LLVM.Int.trunc x narrowW false false hNarrow
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (neg_trunc_neg_refines wideW narrowW hNarrow x
          innerProps.nsw innerProps.nuw truncProps.nsw truncProps.nuw
          outerProps.nsw outerProps.nuw)

end Veir.Passes.InstCombineLLVM.NegateTrunc
