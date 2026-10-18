module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Lemmas
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ComposeBitcastScalar

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

@[local cbv_eval] theorem byteType_cast (t : LLVM.ByteType) :
    (TypeAttr.of LLVM.ByteType t).cast? LLVM.ByteType = some t := IsTypeAttr.cast?_of t

private def intByteSameWidth (input : TypeAttr × TypeAttr) : Bool :=
  match input.1.cast? IntegerType, input.2.cast? LLVM.ByteType with
  | some intTy, some byteTy =>
      decide (intTy.bitwidth = byteTy.bitwidth ∧ 0 < intTy.bitwidth)
  | _, _ => false

/-- `bitcast(bitcast(x : I) : I) : B -> bitcast(x)`, the I-I-B row of
    LLVM's eliminable cast-pair table, for arbitrary equal nonzero widths. -/
public def composeBitcastIIB : Pattern OpCode :=
  Pattern.Builder
    (do
      let intTy ← MatchProg.type (Attr := IntegerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      MatchProg.matchNative (intTy, byteTy) intByteSameWidth
      let x ← MatchProg.value intTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[intTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[byteTy] (fun _ => true)
      return (byteTy, x))
    (fun (byteTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[byteTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastIIB_valid : Pattern.Valid composeBitcastIIB := by
  simp only [composeBitcastIIB]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, integerType_cast, byteType_cast,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ ⟨byteW⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ inner hInner
  obtain rfl := (bitcast_int_iff w x inner).mp hInner
  rintro _ source hSource
  obtain ⟨hw, rfl⟩ := (bitcast_int_byte_iff w byteW x source).mp hSource
  subst byteW
  rintro hWidths
  simp only [intByteSameWidth, IsTypeAttr.cast?_of] at hWidths
  have _hpos : 0 < w := (of_decide_eq_true hWidths).2
  refine ⟨.byte w (LLVM.Byte.fromInt x),
    (bitcast_int_byte_iff w w x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- I-B-I row of the eliminable cast-pair table. -/
public def composeBitcastIBI : Pattern OpCode :=
  Pattern.Builder
    (do
      let intTy ← MatchProg.type (Attr := IntegerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      MatchProg.matchNative (intTy, byteTy) intByteSameWidth
      let x ← MatchProg.value intTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[byteTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[intTy] (fun _ => true)
      return (intTy, x))
    (fun (intTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[intTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastIBI_valid : Pattern.Valid composeBitcastIBI := by
  simp only [composeBitcastIBI]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, integerType_cast, byteType_cast,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ ⟨byteW⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ inner hInner
  obtain ⟨hw, rfl⟩ := (bitcast_int_byte_iff w byteW x inner).mp hInner
  subst byteW
  rintro _ source hSource
  obtain ⟨_, rfl⟩ := (bitcast_byte_int_iff w w (LLVM.Byte.fromInt x) source).mp hSource
  rintro hWidths
  simp only [intByteSameWidth, IsTypeAttr.cast?_of] at hWidths
  have hpos : 0 < w := (of_decide_eq_true hWidths).2
  refine ⟨.int w x, (bitcast_int_iff w x _).mpr rfl, ?_⟩
  rw [LLVM.Byte.toInt_fromInt x hpos]
  exact RuntimeValue.isRefinedBy_refl _

/-- I-B-B row of the eliminable cast-pair table. -/
public def composeBitcastIBB : Pattern OpCode :=
  Pattern.Builder
    (do
      let intTy ← MatchProg.type (Attr := IntegerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      MatchProg.matchNative (intTy, byteTy) intByteSameWidth
      let x ← MatchProg.value intTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[byteTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[byteTy] (fun _ => true)
      return (byteTy, x))
    (fun (byteTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[byteTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastIBB_valid : Pattern.Valid composeBitcastIBB := by
  simp only [composeBitcastIBB]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, integerType_cast, byteType_cast,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ ⟨byteW⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro _ inner hInner
  obtain ⟨hw, rfl⟩ := (bitcast_int_byte_iff w byteW x inner).mp hInner
  subst byteW
  rintro _ source hSource
  obtain ⟨_, rfl⟩ := (bitcast_byte_iff w w (LLVM.Byte.fromInt x) source).mp hSource
  rintro hWidths
  simp only [intByteSameWidth, IsTypeAttr.cast?_of] at hWidths
  refine ⟨.byte w (LLVM.Byte.fromInt x),
    (bitcast_int_byte_iff w w x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- B-I-I row of the eliminable cast-pair table. -/
public def composeBitcastBII : Pattern OpCode :=
  Pattern.Builder
    (do
      let intTy ← MatchProg.type (Attr := IntegerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      MatchProg.matchNative (intTy, byteTy) intByteSameWidth
      let x ← MatchProg.value byteTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[intTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[intTy] (fun _ => true)
      return (intTy, x))
    (fun (intTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[intTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastBII_valid : Pattern.Valid composeBitcastBII := by
  simp only [composeBitcastBII]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, integerType_cast, byteType_cast,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ ⟨byteW⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hX
  rintro _ inner hInner
  obtain ⟨hw, rfl⟩ := (bitcast_byte_int_iff byteW w x inner).mp hInner
  subst byteW
  rintro _ source hSource
  obtain rfl := (bitcast_int_iff w x.toInt source).mp hSource
  rintro hWidths
  simp only [intByteSameWidth, IsTypeAttr.cast?_of] at hWidths
  refine ⟨.int w x.toInt,
    (bitcast_byte_int_iff w w x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- B-I-B row of the eliminable cast-pair table.  Integer poison collapses
    per-bit byte poison, so the composed source refines the direct byte value. -/
public def composeBitcastBIB : Pattern OpCode :=
  Pattern.Builder
    (do
      let intTy ← MatchProg.type (Attr := IntegerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      MatchProg.matchNative (intTy, byteTy) intByteSameWidth
      let x ← MatchProg.value byteTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[intTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[byteTy] (fun _ => true)
      return (byteTy, x))
    (fun (byteTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[byteTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastBIB_valid : Pattern.Valid composeBitcastBIB := by
  simp only [composeBitcastBIB]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, integerType_cast, byteType_cast,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ ⟨byteW⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hX
  rintro _ inner hInner
  obtain ⟨hw, rfl⟩ := (bitcast_byte_int_iff byteW w x inner).mp hInner
  subst byteW
  rintro _ source hSource
  obtain ⟨_, rfl⟩ := (bitcast_int_byte_iff w w x.toInt source).mp hSource
  rintro hWidths
  simp only [intByteSameWidth, IsTypeAttr.cast?_of] at hWidths
  refine ⟨.byte w x, (bitcast_byte_iff w w x _).mpr ⟨rfl, rfl⟩, ?_⟩
  change ∃ h : w = w, (LLVM.Byte.fromInt x.toInt).cast h ⊒ x
  exact ⟨rfl, by simpa only [LLVM.Byte.cast_self] using byte_fromInt_toInt_refines x⟩

/-- B-B-I row of the eliminable cast-pair table. -/
public def composeBitcastBBI : Pattern OpCode :=
  Pattern.Builder
    (do
      let intTy ← MatchProg.type (Attr := IntegerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      MatchProg.matchNative (intTy, byteTy) intByteSameWidth
      let x ← MatchProg.value byteTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[byteTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[intTy] (fun _ => true)
      return (intTy, x))
    (fun (intTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[intTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastBBI_valid : Pattern.Valid composeBitcastBBI := by
  simp only [composeBitcastBBI]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, integerType_cast, byteType_cast,
        HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
        HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ ⟨byteW⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hX
  rintro _ inner hInner
  obtain ⟨_, rfl⟩ := (bitcast_byte_iff byteW byteW x inner).mp hInner
  rintro _ source hSource
  obtain ⟨hw, rfl⟩ := (bitcast_byte_int_iff byteW w x source).mp hSource
  subst byteW
  rintro hWidths
  simp only [intByteSameWidth, IsTypeAttr.cast?_of] at hWidths
  refine ⟨.int w x.toInt,
    (bitcast_byte_int_iff w w x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- B-B-B row of the eliminable cast-pair table. -/
public def composeBitcastBBB : Pattern OpCode :=
  Pattern.Builder
    (do
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      let x ← MatchProg.value byteTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[byteTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[byteTy] (fun _ => true)
      return (byteTy, x))
    (fun (byteTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[byteTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastBBB_valid : Pattern.Valid composeBitcastBBB := by
  simp only [composeBitcastBBB]
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
  rintro ⟨w⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.byteType.mp hX
  rintro _ inner hInner
  obtain ⟨_, rfl⟩ := (bitcast_byte_iff w w x inner).mp hInner
  rintro _ source hSource
  obtain ⟨_, rfl⟩ := (bitcast_byte_iff w w x source).mp hSource
  refine ⟨.byte w x, (bitcast_byte_iff w w x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- Same-address-space P-P-P row of the eliminable cast-pair table.  Puddle's
    scalar pointer type has a single modeled address space. -/
public def composeBitcastPPP : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let x ← MatchProg.value ptrTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[ptrTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[ptrTy] (fun _ => true)
      return (ptrTy, x))
    (fun (ptrTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[ptrTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastPPP_valid : Pattern.Valid composeBitcastPPP := by
  simp only [composeBitcastPPP]
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
  rintro ptrTy x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hX
  rintro _ inner hInner
  obtain rfl := (bitcast_pointer_iff ptrTy x inner).mp hInner
  rintro _ source hSource
  obtain rfl := (bitcast_pointer_iff ptrTy x source).mp hSource
  refine ⟨.addr x, (bitcast_pointer_iff ptrTy x _).mpr rfl, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- P-P-B row: collapse the pointer-preserving inner cast into the direct
    pointer-to-byte bitcast. -/
public def composeBitcastPPB : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      let x ← MatchProg.value ptrTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[ptrTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[byteTy] (fun _ => true)
      return (byteTy, x))
    (fun (byteTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[byteTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastPPB_valid : Pattern.Valid composeBitcastPPB := by
  simp only [composeBitcastPPB]
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
  rintro ptrTy ⟨w⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hX
  rintro _ inner hInner
  obtain rfl := (bitcast_pointer_iff ptrTy x inner).mp hInner
  rintro _ source hSource
  obtain ⟨hw, rfl⟩ := (bitcast_pointer_byte_iff w x source).mp hSource
  subst w
  refine ⟨.byte 64 x.toByte,
    (bitcast_pointer_byte_iff 64 x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- P-B-B row: the outer byte bitcast is an identity. -/
public def composeBitcastPBB : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      let x ← MatchProg.value ptrTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[byteTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[byteTy] (fun _ => true)
      return (byteTy, x))
    (fun (byteTy, x) => do
      let props ← CreateProg.property (.llvm .bitcast) ()
      CreateProg.operation (.llvm .bitcast) #[x] #[byteTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastPBB_valid : Pattern.Valid composeBitcastPBB := by
  simp only [composeBitcastPBB]
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
  rintro ptrTy ⟨w⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hX
  rintro _ inner hInner
  obtain ⟨hw, rfl⟩ := (bitcast_pointer_byte_iff w x inner).mp hInner
  subst w
  rintro _ source hSource
  obtain ⟨_, rfl⟩ := (bitcast_byte_iff 64 64 x.toByte source).mp hSource
  refine ⟨.byte 64 x.toByte,
    (bitcast_pointer_byte_iff 64 x _).mpr ⟨rfl, rfl⟩, ?_⟩
  exact RuntimeValue.isRefinedBy_refl _

/-- P-B-I row of LLVM's table: replace the two bitcasts by `ptrtoint`.
    Both modeled paths expose the pointer address and are memory-independent. -/
public def composeBitcastPBI : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrTy ← MatchProg.type (Attr := LLVM.PointerType)
      let byteTy ← MatchProg.type (Attr := LLVM.ByteType)
      let intTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ptrTy
      let inner ← MatchProg.operation (.llvm .bitcast) #[x] #[byteTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .bitcast) #[inner.res[0]!] #[intTy] (fun _ => true)
      return (intTy, x))
    (fun (intTy, x) => do
      let props ← CreateProg.property (.llvm .ptrtoint) ()
      CreateProg.operation (.llvm .ptrtoint) #[x] #[intTy] props)
    (fun result => result.res[0]!)

public theorem composeBitcastPBI_valid : Pattern.Valid composeBitcastPBI := by
  simp only [composeBitcastPBI]
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
  rintro ptrTy ⟨byteW⟩ ⟨intW, signedness⟩ x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp hX
  rintro _ inner hInner
  obtain ⟨hByte, rfl⟩ := (bitcast_pointer_byte_iff byteW x inner).mp hInner
  subst byteW
  rintro _ source hSource
  obtain ⟨hInt, rfl⟩ := (bitcast_byte_int_iff 64 intW x.toByte source).mp hSource
  subst intW
  refine ⟨.int 64 x.toInt, (ptrtoint_iff x _).mpr rfl, ?_⟩
  rw [ptr_toByte_toInt x]
  exact RuntimeValue.isRefinedBy_refl _

end Veir.Passes.InstCombineLLVM.ComposeBitcastScalar

#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastIIB_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastIBI_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastIBB_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBII_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBIB_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBBI_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastBBB_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPPP_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPPB_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPBB_valid
#print axioms Veir.Passes.InstCombineLLVM.ComposeBitcastScalar.composeBitcastPBI_valid
