module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NegateBooleanExtension

open Veir
open Veir.Data
open Veir.Puddle
open Veir.Passes.InstCombineLLVM

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

/-- Scalar specialization of InstCombineNegator.cpp:186-190:
    `-(sext i1 x) -> zext i1 x`. -/
public def negateSExtI1 : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let extended ← MatchProg.operation (.llvm .sext) #[x] #[dstTy] (fun _ => true)
      let zero ← matchIntConstant dstTy 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, extended.res[0]!] #[dstTy]
        (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem negateSExtI1_valid : Pattern.Valid negateSExtI1 := by
  simp only [negateSExtI1, matchIntConstant]
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
  rintro type ⟨srcW, srcSignedness⟩ hType hWidth
  subst type
  change srcW = 1 at hWidth
  subst srcW
  rintro ⟨dstW, dstSignedness⟩ value hValue
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hValue
  rintro _ extended hExtended
  obtain ⟨hWiden, rfl⟩ := (sext_iff 1 dstW x extended).mp hExtended
  rintro ⟨constantValue⟩ zero hZero hInterpZero
  cases constantValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro negProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rw [hZeroValue]
    refine ⟨.int dstW (LLVM.Int.zext x dstW false hWiden), ?_, ?_⟩
    · exact (zext_iff _ _ _ _ _).mpr ⟨hWiden, rfl⟩
    change ∃ h : dstW = dstW,
      (LLVM.Int.sub (.val (BitVec.ofInt dstW 0)) (LLVM.Int.sext x dstW hWiden)
        negProps.nsw negProps.nuw).cast h ⊒ LLVM.Int.zext x dstW false hWiden
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (isRefinedBy_trans
        (sub_flags_refine dstW (.val (BitVec.ofInt dstW 0))
          (LLVM.Int.sext x dstW hWiden) negProps.nsw negProps.nuw)
        (by rw [neg_sext_i1]; exact isRefinedBy_refl _))

/-- Scalar specialization of InstCombineNegator.cpp:191-195:
    `-(zext i1 x) -> sext i1 x`.  Any matched `nneg` flag is accounted for as
    source poison and is absent from the replacement `sext`. -/
public def negateZExtI1 : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let extended ← MatchProg.operation (.llvm .zext) #[x] #[dstTy] (fun _ => true)
      let zero ← matchIntConstant dstTy 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, extended.res[0]!] #[dstTy]
        (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem negateZExtI1_valid : Pattern.Valid negateZExtI1 := by
  simp only [negateZExtI1, matchIntConstant]
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
  rintro type ⟨srcW, srcSignedness⟩ hType hWidth
  subst type
  change srcW = 1 at hWidth
  subst srcW
  rintro ⟨dstW, dstSignedness⟩ value hValue
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hValue
  rintro zextProps extended hExtended
  obtain ⟨hWiden, rfl⟩ := (zext_iff 1 dstW zextProps x extended).mp hExtended
  rintro ⟨constantValue⟩ zero hZero hInterpZero
  cases constantValue with
  | float _ | dense _ | string _ => simp at hZero
  | integer zeroAttr =>
    have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
    obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
    rintro negProps source hSource
    obtain rfl := (sub_iff _ _ _ _ _).mp hSource
    rw [hZeroValue]
    refine ⟨.int dstW (LLVM.Int.sext x dstW hWiden), ?_, ?_⟩
    · exact (sext_iff _ _ _ _).mpr ⟨hWiden, rfl⟩
    change ∃ h : dstW = dstW,
      (LLVM.Int.sub (.val (BitVec.ofInt dstW 0))
        (LLVM.Int.zext x dstW zextProps.nneg hWiden)
        negProps.nsw negProps.nuw).cast h ⊒ LLVM.Int.sext x dstW hWiden
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self] using
      (isRefinedBy_trans
        (sub_flags_refine dstW (.val (BitVec.ofInt dstW 0))
          (LLVM.Int.zext x dstW zextProps.nneg hWiden) negProps.nsw negProps.nuw)
        (isRefinedBy_trans
          (neg_refine_mono dstW (zext_nneg_refines dstW hWiden x zextProps.nneg))
          (by rw [neg_zext_i1]; exact isRefinedBy_refl _)))

end Veir.Passes.InstCombineLLVM.NegateBooleanExtension
