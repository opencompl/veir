module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ComposeZExt

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def sourceLtDest (input : TypeAttr × TypeAttr) : Bool :=
  match input.1.cast? IntegerType, input.2.cast? IntegerType with
  | some src, some dst => src.bitwidth < dst.bitwidth
  | _, _ => false

private def sourceGtDest (input : TypeAttr × TypeAttr) : Bool :=
  match input.1.cast? IntegerType, input.2.cast? IntegerType with
  | some src, some dst => dst.bitwidth < src.bitwidth
  | _, _ => false

private def sourceEqDest (input : TypeAttr × TypeAttr) : Bool :=
  match input.1.cast? IntegerType, input.2.cast? IntegerType with
  | some src, some dst => src.bitwidth = dst.bitwidth
  | _, _ => false

/-- The scalar zext/zext entry of the eliminable cast-pair table used at
    InstCombineCasts.cpp:235-243, for arbitrary strictly increasing widths.
    Both matched `nneg` flags are accepted and the direct replacement clears nneg. -/
public def composeZExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .zext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .zext) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

private theorem compose_zext_refines {s m d : Nat} (hsm : s < m) (hmd : m < d)
    (x : LLVM.Int s)
    (innerNneg outerNneg : Bool) :
    LLVM.Int.zext (LLVM.Int.zext x m innerNneg hsm) d outerNneg hmd ⊒
      LLVM.Int.zext x d false (by omega) := by
  apply isRefinedBy_trans (zext_flag_refines hmd _ outerNneg)
  apply isRefinedBy_trans (LLVM.Int.zext_mono _ _ hmd
    (zext_flag_refines hsm x innerNneg))
  cases x with
  | poison => simp [LLVM.Int.zext, Id.run]
  | val x =>
    have hcomp : (x.setWidth m).setWidth d = x.setWidth d :=
      BitVec.setWidth_setWidth (by omega)
    simp [LLVM.Int.zext, Id.run, hcomp]

public theorem composeZExt_valid : Pattern.Valid composeZExt := by
  simp only [composeZExt]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro innerProps inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ :=
    (zext_iff srcW middleW innerProps x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hMiddleDst, rfl⟩ :=
    (zext_iff middleW dstW outerProps _ source).mp hSource
  have hSrcDst : srcW < dstW := Nat.lt_trans hSrcMiddle hMiddleDst
  refine ⟨.int dstW (LLVM.Int.zext x dstW false hSrcDst), ?_, ?_⟩
  · exact (zext_iff srcW dstW { nneg := false } x _).mpr ⟨hSrcDst, rfl⟩
  change ∃ h : dstW = dstW,
    (LLVM.Int.zext (LLVM.Int.zext x middleW innerProps.nneg hSrcMiddle)
      dstW outerProps.nneg hMiddleDst).cast h ⊒ LLVM.Int.zext x dstW false _
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    compose_zext_refines hSrcMiddle hMiddleDst x innerProps.nneg outerProps.nneg

/-- Scalar `trunc(trunc(x))` row of LLVM's eliminable cast-pair table. -/
public def composeTrunc : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .trunc) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) { nsw := false, nuw := false }
      CreateProg.operation (.llvm .trunc) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeTrunc_valid : Pattern.Valid composeTrunc := by
  simp only [composeTrunc]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro innerProps inner hInner
  obtain ⟨hMiddleSrc, rfl⟩ :=
    (trunc_iff srcW middleW innerProps x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  refine ⟨.int dstW (LLVM.Int.trunc x dstW false false (by omega)), ?_, ?_⟩
  · exact (trunc_iff srcW dstW default x _).mpr ⟨by omega, rfl⟩
  change ∃ h : dstW = dstW,
    (LLVM.Int.trunc (LLVM.Int.trunc x middleW innerProps.nsw innerProps.nuw
      hMiddleSrc) dstW outerProps.nsw outerProps.nuw hDstMiddle).cast h ⊒
      LLVM.Int.trunc x dstW false false _
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_trunc_refines hDstMiddle hMiddleSrc x
    innerProps.nsw innerProps.nuw outerProps.nsw outerProps.nuw

/-- Scalar `sext(sext(x))` row of LLVM's eliminable cast-pair table. -/
public def composeSExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .sext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .sext) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeSExt_valid : Pattern.Valid composeSExt := by
  simp only [composeSExt]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ := (sext_iff srcW middleW x inner).mp hInner
  rintro _ source hSource
  obtain ⟨hMiddleDst, rfl⟩ := (sext_iff middleW dstW _ source).mp hSource
  refine ⟨.int dstW (LLVM.Int.sext x dstW (by omega)), ?_, ?_⟩
  · exact (sext_iff srcW dstW x _).mpr ⟨by omega, rfl⟩
  change ∃ h : dstW = dstW,
    (LLVM.Int.sext (LLVM.Int.sext x middleW hSrcMiddle)
      dstW hMiddleDst).cast h ⊒ LLVM.Int.sext x dstW _
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    compose_sext_refines hSrcMiddle hMiddleDst x

/-- Scalar `sext(zext(x)) -> zext(x)` row of LLVM's eliminable cast-pair table. -/
public def composeZExtSExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .zext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .sext) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeZExtSExt_valid : Pattern.Valid composeZExtSExt := by
  simp only [composeZExtSExt]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro innerProps inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ :=
    (zext_iff srcW middleW innerProps x inner).mp hInner
  rintro _ source hSource
  obtain ⟨hMiddleDst, rfl⟩ := (sext_iff middleW dstW _ source).mp hSource
  refine ⟨.int dstW (LLVM.Int.zext x dstW false (by omega)), ?_, ?_⟩
  · exact (zext_iff srcW dstW { nneg := false } x _).mpr ⟨by omega, rfl⟩
  change ∃ h : dstW = dstW,
    (LLVM.Int.sext (LLVM.Int.zext x middleW innerProps.nneg hSrcMiddle)
      dstW hMiddleDst).cast h ⊒ LLVM.Int.zext x dstW false _
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    compose_zext_sext_refines hSrcMiddle hMiddleDst x innerProps.nneg

/-- `trunc(zext(x)) -> zext(x)` when the destination remains wider than the source. -/
public def composeZExtTruncToZExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, dstTy) sourceLtDest
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .zext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeZExtTruncToZExt_valid : Pattern.Valid composeZExtTruncToZExt := by
  simp only [composeZExtTruncToZExt]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, integerType_cast,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro innerProps inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ :=
    (zext_iff srcW middleW innerProps x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  rintro hWidths
  simp only [sourceLtDest, IsTypeAttr.cast?_of] at hWidths
  have hSrcDst : srcW < dstW := of_decide_eq_true hWidths
  refine ⟨.int dstW (LLVM.Int.zext x dstW false hSrcDst), ?_, ?_⟩
  · exact (zext_iff srcW dstW { nneg := false } x _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_zext_trunc_to_zext_refines
    hSrcMiddle hSrcDst hDstMiddle x innerProps.nneg outerProps.nsw outerProps.nuw

/-- `trunc(zext(x)) -> trunc(x)` when the destination is narrower than the source. -/
public def composeZExtTruncToTrunc : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, dstTy) sourceGtDest
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .zext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) { nsw := false, nuw := false }
      CreateProg.operation (.llvm .trunc) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeZExtTruncToTrunc_valid : Pattern.Valid composeZExtTruncToTrunc := by
  simp only [composeZExtTruncToTrunc]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, integerType_cast,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro innerProps inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ :=
    (zext_iff srcW middleW innerProps x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  rintro hWidths
  simp only [sourceGtDest, IsTypeAttr.cast?_of] at hWidths
  have hDstSrc : dstW < srcW := of_decide_eq_true hWidths
  refine ⟨.int dstW (LLVM.Int.trunc x dstW false false hDstSrc), ?_, ?_⟩
  · exact (trunc_iff srcW dstW default x _).mpr ⟨hDstSrc, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_zext_trunc_to_trunc_refines
    hSrcMiddle hDstSrc x innerProps.nneg outerProps.nsw outerProps.nuw

/-- `trunc(zext(x)) -> bitcast(x)` when source and destination widths are equal. -/
public def composeZExtTruncToBitcast : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, dstTy) sourceEqDest
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .zext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeZExtTruncToBitcast_valid : Pattern.Valid composeZExtTruncToBitcast := by
  simp only [composeZExtTruncToBitcast]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, integerType_cast,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro innerProps inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ :=
    (zext_iff srcW middleW innerProps x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  rintro hWidths
  simp only [sourceEqDest, IsTypeAttr.cast?_of] at hWidths
  have hEq : srcW = dstW := of_decide_eq_true hWidths
  subst dstW
  refine ⟨.int srcW x, (bitcast_int_iff srcW x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_zext_trunc_to_bitcast_refines
    hSrcMiddle x innerProps.nneg outerProps.nsw outerProps.nuw

/-- `trunc(sext(x)) -> sext(x)` when the destination remains wider than the source. -/
public def composeSExtTruncToSExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, dstTy) sourceLtDest
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .sext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeSExtTruncToSExt_valid : Pattern.Valid composeSExtTruncToSExt := by
  simp only [composeSExtTruncToSExt]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, integerType_cast,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ := (sext_iff srcW middleW x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  rintro hWidths
  simp only [sourceLtDest, IsTypeAttr.cast?_of] at hWidths
  have hSrcDst : srcW < dstW := of_decide_eq_true hWidths
  refine ⟨.int dstW (LLVM.Int.sext x dstW hSrcDst), ?_, ?_⟩
  · exact (sext_iff srcW dstW x _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_sext_trunc_to_sext_refines
    hSrcMiddle hSrcDst hDstMiddle x outerProps.nsw outerProps.nuw

/-- `trunc(sext(x)) -> trunc(x)` when the destination is narrower than the source. -/
public def composeSExtTruncToTrunc : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, dstTy) sourceGtDest
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .sext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) { nsw := false, nuw := false }
      CreateProg.operation (.llvm .trunc) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeSExtTruncToTrunc_valid : Pattern.Valid composeSExtTruncToTrunc := by
  simp only [composeSExtTruncToTrunc]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, integerType_cast,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ := (sext_iff srcW middleW x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  rintro hWidths
  simp only [sourceGtDest, IsTypeAttr.cast?_of] at hWidths
  have hDstSrc : dstW < srcW := of_decide_eq_true hWidths
  refine ⟨.int dstW (LLVM.Int.trunc x dstW false false hDstSrc), ?_, ?_⟩
  · exact (trunc_iff srcW dstW default x _).mpr ⟨hDstSrc, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_sext_trunc_to_trunc_refines
    hSrcMiddle hDstSrc x outerProps.nsw outerProps.nuw

/-- `trunc(sext(x)) -> bitcast(x)` when source and destination widths are equal. -/
public def composeSExtTruncToBitcast : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let middleTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      MatchProg.matchNative (srcTy, dstTy) sourceEqDest
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .sext) #[x] #[middleTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeSExtTruncToBitcast_valid : Pattern.Valid composeSExtTruncToBitcast := by
  simp only [composeSExtTruncToBitcast]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, integerType_cast,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨srcW, srcSignedness⟩ ⟨middleW, middleSignedness⟩
    ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain ⟨hSrcMiddle, rfl⟩ := (sext_iff srcW middleW x inner).mp hInner
  rintro outerProps source hSource
  obtain ⟨hDstMiddle, rfl⟩ :=
    (trunc_iff middleW dstW outerProps _ source).mp hSource
  rintro hWidths
  simp only [sourceEqDest, IsTypeAttr.cast?_of] at hWidths
  have hEq : srcW = dstW := of_decide_eq_true hWidths
  subst dstW
  refine ⟨.int srcW x, (bitcast_int_iff srcW x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using compose_sext_trunc_to_bitcast_refines
    hSrcMiddle x outerProps.nsw outerProps.nuw

/-- Scalar trunc followed by a same-type integer bitcast. -/
public def composeTruncBitcast : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .trunc) #[x] #[dstTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) { nsw := false, nuw := false }
      CreateProg.operation (.llvm .trunc) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeTruncBitcast_valid : Pattern.Valid composeTruncBitcast := by
  simp only [composeTruncBitcast]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro truncProps inner hInner
  obtain ⟨hDstSrc, rfl⟩ := (trunc_iff srcW dstW truncProps x inner).mp hInner
  rintro _ source hSource
  obtain rfl := (bitcast_int_iff dstW _ source).mp hSource
  refine ⟨.int dstW (LLVM.Int.trunc x dstW false false hDstSrc), ?_, ?_⟩
  · exact (trunc_iff srcW dstW default x _).mpr ⟨hDstSrc, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    trunc_flags_refine srcW dstW hDstSrc x truncProps.nsw truncProps.nuw

/-- Scalar zext followed by a same-type integer bitcast. -/
public def composeZExtBitcast : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .zext) #[x] #[dstTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeZExtBitcast_valid : Pattern.Valid composeZExtBitcast := by
  simp only [composeZExtBitcast]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro zextProps inner hInner
  obtain ⟨hSrcDst, rfl⟩ := (zext_iff srcW dstW zextProps x inner).mp hInner
  rintro _ source hSource
  obtain rfl := (bitcast_int_iff dstW _ source).mp hSource
  refine ⟨.int dstW (LLVM.Int.zext x dstW false hSrcDst), ?_, ?_⟩
  · exact (zext_iff srcW dstW { nneg := false } x _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using zext_flag_refines hSrcDst x zextProps.nneg

/-- Scalar sext followed by a same-type integer bitcast. -/
public def composeSExtBitcast : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .sext) #[x] #[dstTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeSExtBitcast_valid : Pattern.Valid composeSExtBitcast := by
  simp only [composeSExtBitcast]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain ⟨hSrcDst, rfl⟩ := (sext_iff srcW dstW x inner).mp hInner
  rintro _ source hSource
  obtain rfl := (bitcast_int_iff dstW _ source).mp hSource
  refine ⟨.int dstW (LLVM.Int.sext x dstW hSrcDst), ?_, ?_⟩
  · exact (sext_iff srcW dstW x _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (isRefinedBy_refl (LLVM.Int.sext x dstW hSrcDst))

/-- A same-type scalar integer bitcast followed by truncation. -/
public def composeBitcastTrunc : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[srcTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .trunc) { nsw := false, nuw := false }
      CreateProg.operation (.llvm .trunc) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastTrunc_valid : Pattern.Valid composeBitcastTrunc := by
  simp only [composeBitcastTrunc]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain rfl := (bitcast_int_iff srcW x inner).mp hInner
  rintro truncProps source hSource
  obtain ⟨hDstSrc, rfl⟩ := (trunc_iff srcW dstW truncProps x source).mp hSource
  refine ⟨.int dstW (LLVM.Int.trunc x dstW false false hDstSrc), ?_, ?_⟩
  · exact (trunc_iff srcW dstW default x _).mpr ⟨hDstSrc, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    trunc_flags_refine srcW dstW hDstSrc x truncProps.nsw truncProps.nuw

/-- A same-type scalar integer bitcast followed by zero extension. -/
public def composeBitcastZExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[srcTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .zext) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .zext) { nneg := false }
      CreateProg.operation (.llvm .zext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastZExt_valid : Pattern.Valid composeBitcastZExt := by
  simp only [composeBitcastZExt]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain rfl := (bitcast_int_iff srcW x inner).mp hInner
  rintro zextProps source hSource
  obtain ⟨hSrcDst, rfl⟩ := (zext_iff srcW dstW zextProps x source).mp hSource
  refine ⟨.int dstW (LLVM.Int.zext x dstW false hSrcDst), ?_, ?_⟩
  · exact (zext_iff srcW dstW { nneg := false } x _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using zext_flag_refines hSrcDst x zextProps.nneg

/-- A same-type scalar integer bitcast followed by sign extension. -/
public def composeBitcastSExt : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcTy ← MatchProg.type (Attr := IntegerType)
      let dstTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value srcTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[srcTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .sext) #[inner.res[0]!] #[dstTy] (fun _ => true)
      return (dstTy, x))
    (fun (dstTy, x) => do
      let props ← CreateProg.property (.llvm .sext) ()
      CreateProg.operation (.llvm .sext) #[x] #[dstTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastSExt_valid : Pattern.Valid composeBitcastSExt := by
  simp only [composeBitcastSExt]
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
  rintro ⟨srcW, srcSignedness⟩ ⟨dstW, dstSignedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  change LLVM.Int srcW at x
  rintro _ inner hInner
  obtain rfl := (bitcast_int_iff srcW x inner).mp hInner
  rintro _ source hSource
  obtain ⟨hSrcDst, rfl⟩ := (sext_iff srcW dstW x source).mp hSource
  refine ⟨.int dstW (LLVM.Int.sext x dstW hSrcDst), ?_, ?_⟩
  · exact (sext_iff srcW dstW x _).mpr ⟨hSrcDst, rfl⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    (isRefinedBy_refl (LLVM.Int.sext x dstW hSrcDst))

/-- Two same-type scalar integer bitcasts collapse to one. -/
public def composeBitcastBitcast : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[ty] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[ty] (fun _ => true)
      return (ty, x))
    (fun (ty, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[ty] props)
    (fun result => result.res[0]!)

public theorem composeBitcastBitcast_valid : Pattern.Valid composeBitcastBitcast := by
  simp only [composeBitcastBitcast]
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
  change LLVM.Int w at x
  rintro _ inner hInner
  obtain rfl := (bitcast_int_iff w x inner).mp hInner
  rintro _ source hSource
  obtain rfl := (bitcast_int_iff w x source).mp hSource
  refine ⟨.int w x, (bitcast_int_iff w x _).mpr rfl, ?_⟩
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using (isRefinedBy_refl x)

end Veir.Passes.InstCombineLLVM.ComposeZExt

#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeTrunc_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtSExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtTruncToZExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtTruncToTrunc_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtTruncToBitcast_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtTruncToSExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtTruncToTrunc_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtTruncToBitcast_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeTruncBitcast_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeZExtBitcast_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeSExtBitcast_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastTrunc_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastZExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastSExt_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeZExt.composeBitcastBitcast_valid
