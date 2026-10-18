module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticShiftSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.MulShiftConstant

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def isInRangeAmount
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, props) := input
  match type.cast? IntegerType, (asLLVMConstantProperties props).value with
  | some intType, .integer amount =>
      decide ((BitVec.ofInt intType.bitwidth amount.value).toNat < intType.bitwidth)
  | _, _ => false

private def shiftedConstantProperties
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant) ×
      propertiesOf (OpCode.llvm .mlir__constant)) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let (type, multiplierProps, amountProps) := input
  let some intType := type.cast? IntegerType | none
  let .integer multiplier := (asLLVMConstantProperties multiplierProps).value | none
  let .integer amount := (asLLVMConstantProperties amountProps).value | none
  let folded := BitVec.ofInt intType.bitwidth multiplier.value <<<
    BitVec.ofInt intType.bitwidth amount.value
  return LLVMConstantProperties.mk
    (.integer (IntegerAttr.ofInt (folded.toNat : Int) intType))

private def shiftedConstantNotSignedMin
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant) ×
      propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, multiplierProps, amountProps) := input
  match type.cast? IntegerType,
      (asLLVMConstantProperties multiplierProps).value,
      (asLLVMConstantProperties amountProps).value with
  | some intType, .integer multiplier, .integer amount =>
      decide (BitVec.ofInt intType.bitwidth multiplier.value <<<
        BitVec.ofInt intType.bitwidth amount.value ≠ BitVec.intMin intType.bitwidth)
  | _, _, _ => false

private def shiftedConstantsValidForNSW
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant) ×
      propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, multiplierProps, amountProps) := input
  isInRangeAmount (type, amountProps) &&
    shiftedConstantNotSignedMin (type, multiplierProps, amountProps)

/-- Unflagged scalar specialization of InstCombineMulDivRem.cpp:233-252:
    `(X << C2) * C1 -> X * (C1 << C2)`. -/
public def mulShiftConstant : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    MatchProg.matchNative (ty, amount.properties) isInRangeAmount
    let shifted ← MatchProg.operation (.llvm .shl) #[x, amount.res[0]!] #[ty]
      (fun p => !p.nsw && !p.nuw)
    let multiplier ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    let _ ← MatchProg.root (.llvm .mul) #[shifted.res[0]!, multiplier.res[0]!] #[ty]
      (fun p => !p.nsw && !p.nuw)
    return (ty, x, multiplier.properties, amount.properties))
  (fun (ty, x, multiplierProps, amountProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, multiplierProps, amountProps) shiftedConstantProperties
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let mp ← CreateProg.property (.llvm .mul) default
    CreateProg.operation (.llvm .mul) #[x, folded.res[0]!] #[ty] mp)
  (fun result => result.res[0]!)

/-- Source specialization with an unflagged outer multiply and arbitrary inner
    shift flags. LLVM propagates neither nowrap flag in this case. -/
public def mulShiftConstantOuterUnflagged : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    MatchProg.matchNative (ty, amount.properties) isInRangeAmount
    let shifted ← MatchProg.operation (.llvm .shl) #[x, amount.res[0]!] #[ty]
      (fun _ => true)
    let multiplier ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    let _ ← MatchProg.root (.llvm .mul) #[shifted.res[0]!, multiplier.res[0]!]
      #[ty] (fun p => !p.nsw && !p.nuw)
    return (ty, x, multiplier.properties, amount.properties))
  (fun (ty, x, multiplierProps, amountProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, multiplierProps, amountProps) shiftedConstantProperties
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let mp ← CreateProg.property (.llvm .mul) default
    CreateProg.operation (.llvm .mul) #[x, folded.res[0]!] #[ty] mp)
  (fun result => result.res[0]!)

/-- Source specialization where both the inner shift and outer multiply carry
    `nuw`; LLVM propagates `nuw` to the reassociated multiply. The `nsw` bits
    of the source operations are independent of this unsigned proof. -/
public def mulShiftConstantNUW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    MatchProg.matchNative (ty, amount.properties) isInRangeAmount
    let shifted ← MatchProg.operation (.llvm .shl) #[x, amount.res[0]!] #[ty]
      (fun p => p.nuw)
    let multiplier ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    let _ ← MatchProg.root (.llvm .mul) #[shifted.res[0]!, multiplier.res[0]!]
      #[ty] (fun p => p.nuw)
    return (ty, x, multiplier.properties, amount.properties))
  (fun (ty, x, multiplierProps, amountProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, multiplierProps, amountProps) shiftedConstantProperties
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let mp ← CreateProg.property (.llvm .mul) { nsw := false, nuw := true }
    CreateProg.operation (.llvm .mul) #[x, folded.res[0]!] #[ty] mp)
  (fun result => result.res[0]!)

/-- Source specialization where both the inner shift and outer multiply carry
    `nsw` and the folded constant is not signed minimum. -/
public def mulShiftConstantNSW : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] isIntegralConstant
    let shifted ← MatchProg.operation (.llvm .shl) #[x, amount.res[0]!] #[ty]
      (fun p => p.nsw)
    let multiplier ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    MatchProg.matchNative (ty, multiplier.properties, amount.properties)
      shiftedConstantsValidForNSW
    let _ ← MatchProg.root (.llvm .mul) #[shifted.res[0]!, multiplier.res[0]!]
      #[ty] (fun p => p.nsw)
    return (ty, x, multiplier.properties, amount.properties))
  (fun (ty, x, multiplierProps, amountProps) => do
    let foldedProps ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      (ty, multiplierProps, amountProps) shiftedConstantProperties
    let folded ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] foldedProps
    let mp ← CreateProg.property (.llvm .mul) { nsw := true, nuw := false }
    CreateProg.operation (.llvm .mul) #[x, folded.res[0]!] #[ty] mp)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
public theorem mulShiftConstant_valid : Pattern.Valid mulShiftConstant := by
  simp only [mulShiftConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpScalarPropertyPuddleSemantics
  rintro ⟨w, signedness⟩ x
  rintro amountProps amount hAmount hInterpAmount
  generalize hTypedAmount : asLLVMConstantProperties amountProps = typedAmount
  cases typedAmount with
  | mk amountValue => cases amountValue with
    | float _ | dense _ | string _ =>
      simp [isIntegralConstant, hTypedAmount] at hAmount
    | integer amountAttr =>
      have hInterpAmountTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties amountProps) #[IntegerType.mk w signedness]
          #[] #[amount] := hInterpAmount
      rw [hTypedAmount] at hInterpAmountTyped
      obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmountTyped
      rintro shiftProps shifted hShiftNSW hShiftNUW hShifted
      obtain rfl := (shl_iff _ shiftProps _ _ _).mp hShifted
      rintro multiplierProps multiplier hMultiplier hInterpMultiplier
      generalize hTypedMultiplier :
          asLLVMConstantProperties multiplierProps = typedMultiplier
      cases typedMultiplier with
      | mk multiplierValue => cases multiplierValue with
        | float _ | dense _ | string _ =>
          simp [isIntegralConstant, hTypedMultiplier] at hMultiplier
        | integer multiplierAttr =>
          have hInterpMultiplierTyped : InterpretsTo (.llvm .mlir__constant)
              (asLLVMConstantProperties multiplierProps) #[IntegerType.mk w signedness]
              #[] #[multiplier] := hInterpMultiplier
          rw [hTypedMultiplier] at hInterpMultiplierTyped
          obtain rfl := (constant_iff _ multiplierAttr _).mp hInterpMultiplierTyped
          rintro mulProps source hMulNSW hMulNUW hSource hInRange
          obtain rfl := (mul_iff _ _ _ _ _).mp hSource
          have hAmountValue :
              amountProps.value = LLVMConstantValue.integer amountAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedAmount
          have hMultiplierValue :
              multiplierProps.value = LLVMConstantValue.integer multiplierAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedMultiplier
          have hRange : (BitVec.ofInt w amountAttr.value).toNat < w := by
            simpa [isInRangeAmount, hAmountValue, asLLVMConstantProperties,
              IsTypeAttr.cast?_of] using hInRange
          rw [hShiftNSW, hShiftNUW, hMulNSW, hMulNUW]
          simp [shiftedConstantProperties, hTypedAmount, hTypedMultiplier,
            IsTypeAttr.cast?_of]
          let folded := BitVec.ofInt w multiplierAttr.value <<<
            BitVec.ofInt w amountAttr.value
          have hFoldedConstant : folded = BitVec.ofInt w
              (IntegerAttr.normalizeValue
                { bitwidth := w, signedness := signedness }
                (folded.toNat : Int)) := by
            calc
              folded = BitVec.ofInt w (folded.toNat : Int) := by
                rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              _ = BitVec.ofInt w
                    (IntegerAttr.normalizeValue
                      { bitwidth := w, signedness := signedness }
                      (folded.toNat : Int)) :=
                (ofInt_normalizeValue
                  { bitwidth := w, signedness := signedness }
                  (folded.toNat : Int)).symm
          refine ⟨.int w (.val folded), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [folded, IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z)) hFoldedConstant
          refine ⟨.int w (LLVM.Int.mul x (.val folded)), ?_, ?_⟩
          · exact (mul_iff _ _ _ _ _).mpr rfl
          refine ⟨rfl, ?_⟩
          simpa only [folded, LLVM.Int.cast_self] using
            (mul_shift_constant_refines w x
              (BitVec.ofInt w multiplierAttr.value)
              (BitVec.ofInt w amountAttr.value) hRange)

set_option linter.tacticCheckInstances false in
public theorem mulShiftConstantOuterUnflagged_valid :
    Pattern.Valid mulShiftConstantOuterUnflagged := by
  simp only [mulShiftConstantOuterUnflagged]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpScalarPropertyPuddleSemantics
  rintro ⟨w, signedness⟩ x
  rintro amountProps amount hAmount hInterpAmount
  generalize hTypedAmount : asLLVMConstantProperties amountProps = typedAmount
  cases typedAmount with
  | mk amountValue => cases amountValue with
    | float _ | dense _ | string _ =>
      simp [isIntegralConstant, hTypedAmount] at hAmount
    | integer amountAttr =>
      have hInterpAmountTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties amountProps) #[IntegerType.mk w signedness]
          #[] #[amount] := hInterpAmount
      rw [hTypedAmount] at hInterpAmountTyped
      obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmountTyped
      rintro shiftProps shifted hShifted
      obtain rfl := (shl_iff _ shiftProps _ _ _).mp hShifted
      rintro multiplierProps multiplier hMultiplier hInterpMultiplier
      generalize hTypedMultiplier :
          asLLVMConstantProperties multiplierProps = typedMultiplier
      cases typedMultiplier with
      | mk multiplierValue => cases multiplierValue with
        | float _ | dense _ | string _ =>
          simp [isIntegralConstant, hTypedMultiplier] at hMultiplier
        | integer multiplierAttr =>
          have hInterpMultiplierTyped : InterpretsTo (.llvm .mlir__constant)
              (asLLVMConstantProperties multiplierProps) #[IntegerType.mk w signedness]
              #[] #[multiplier] := hInterpMultiplier
          rw [hTypedMultiplier] at hInterpMultiplierTyped
          obtain rfl := (constant_iff _ multiplierAttr _).mp hInterpMultiplierTyped
          rintro mulProps source hMulNSW hMulNUW hSource hInRange
          obtain rfl := (mul_iff _ _ _ _ _).mp hSource
          have hAmountValue :
              amountProps.value = LLVMConstantValue.integer amountAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedAmount
          have hMultiplierValue :
              multiplierProps.value = LLVMConstantValue.integer multiplierAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedMultiplier
          have hRange : (BitVec.ofInt w amountAttr.value).toNat < w := by
            simpa [isInRangeAmount, hAmountValue, asLLVMConstantProperties,
              IsTypeAttr.cast?_of] using hInRange
          simp [shiftedConstantProperties, hTypedAmount, hTypedMultiplier,
            IsTypeAttr.cast?_of]
          let folded := BitVec.ofInt w multiplierAttr.value <<<
            BitVec.ofInt w amountAttr.value
          have hFoldedConstant : folded = BitVec.ofInt w
              (IntegerAttr.normalizeValue
                { bitwidth := w, signedness := signedness }
                (folded.toNat : Int)) := by
            calc
              folded = BitVec.ofInt w (folded.toNat : Int) := by
                rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              _ = BitVec.ofInt w
                    (IntegerAttr.normalizeValue
                      { bitwidth := w, signedness := signedness }
                      (folded.toNat : Int)) :=
                (ofInt_normalizeValue
                  { bitwidth := w, signedness := signedness }
                  (folded.toNat : Int)).symm
          refine ⟨.int w (.val folded), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [folded, IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z)) hFoldedConstant
          refine ⟨.int w (LLVM.Int.mul x (.val folded)), ?_, ?_⟩
          · exact (mul_iff _ _ _ _ _).mpr rfl
          refine ⟨rfl, ?_⟩
          simpa only [folded, LLVM.Int.cast_self] using
            (mul_shift_constant_drop_flags_refines w x
              (BitVec.ofInt w multiplierAttr.value)
              (BitVec.ofInt w amountAttr.value) hRange shiftProps.nsw
              shiftProps.nuw mulProps.nsw mulProps.nuw)

set_option linter.tacticCheckInstances false in
public theorem mulShiftConstantNUW_valid : Pattern.Valid mulShiftConstantNUW := by
  simp only [mulShiftConstantNUW]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpScalarPropertyPuddleSemantics
  rintro ⟨w, signedness⟩ x
  rintro amountProps amount hAmount hInterpAmount
  generalize hTypedAmount : asLLVMConstantProperties amountProps = typedAmount
  cases typedAmount with
  | mk amountValue => cases amountValue with
    | float _ | dense _ | string _ =>
      simp [isIntegralConstant, hTypedAmount] at hAmount
    | integer amountAttr =>
      have hInterpAmountTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties amountProps) #[IntegerType.mk w signedness]
          #[] #[amount] := hInterpAmount
      rw [hTypedAmount] at hInterpAmountTyped
      obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmountTyped
      rintro shiftProps shifted hShiftNUW hShifted
      obtain rfl := (shl_iff _ shiftProps _ _ _).mp hShifted
      rintro multiplierProps multiplier hMultiplier hInterpMultiplier
      generalize hTypedMultiplier :
          asLLVMConstantProperties multiplierProps = typedMultiplier
      cases typedMultiplier with
      | mk multiplierValue => cases multiplierValue with
        | float _ | dense _ | string _ =>
          simp [isIntegralConstant, hTypedMultiplier] at hMultiplier
        | integer multiplierAttr =>
          have hInterpMultiplierTyped : InterpretsTo (.llvm .mlir__constant)
              (asLLVMConstantProperties multiplierProps) #[IntegerType.mk w signedness]
              #[] #[multiplier] := hInterpMultiplier
          rw [hTypedMultiplier] at hInterpMultiplierTyped
          obtain rfl := (constant_iff _ multiplierAttr _).mp hInterpMultiplierTyped
          rintro mulProps source hMulNUW hSource hInRange
          obtain rfl := (mul_iff _ _ _ _ _).mp hSource
          have hAmountValue :
              amountProps.value = LLVMConstantValue.integer amountAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedAmount
          have hMultiplierValue :
              multiplierProps.value = LLVMConstantValue.integer multiplierAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedMultiplier
          have hRange : (BitVec.ofInt w amountAttr.value).toNat < w := by
            simpa [isInRangeAmount, hAmountValue, asLLVMConstantProperties,
              IsTypeAttr.cast?_of] using hInRange
          rw [hShiftNUW, hMulNUW]
          simp [shiftedConstantProperties, hTypedAmount, hTypedMultiplier,
            IsTypeAttr.cast?_of]
          let folded := BitVec.ofInt w multiplierAttr.value <<<
            BitVec.ofInt w amountAttr.value
          have hFoldedConstant : folded = BitVec.ofInt w
              (IntegerAttr.normalizeValue
                { bitwidth := w, signedness := signedness }
                (folded.toNat : Int)) := by
            calc
              folded = BitVec.ofInt w (folded.toNat : Int) := by
                rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              _ = BitVec.ofInt w
                    (IntegerAttr.normalizeValue
                      { bitwidth := w, signedness := signedness }
                      (folded.toNat : Int)) :=
                (ofInt_normalizeValue
                  { bitwidth := w, signedness := signedness }
                  (folded.toNat : Int)).symm
          refine ⟨.int w (.val folded), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [folded, IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z)) hFoldedConstant
          refine ⟨.int w (LLVM.Int.mul x (.val folded) false true), ?_, ?_⟩
          · exact (mul_iff _ _ _ _ _).mpr rfl
          refine ⟨rfl, ?_⟩
          simpa only [folded, LLVM.Int.cast_self] using
            (mul_shift_constant_nuw_refines w x
              (BitVec.ofInt w multiplierAttr.value)
              (BitVec.ofInt w amountAttr.value) hRange shiftProps.nsw mulProps.nsw)

set_option linter.tacticCheckInstances false in
public theorem mulShiftConstantNSW_valid : Pattern.Valid mulShiftConstantNSW := by
  simp only [mulShiftConstantNSW]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpScalarPropertyPuddleSemantics
  rintro ⟨w, signedness⟩ x
  rintro amountProps amount hAmount hInterpAmount
  generalize hTypedAmount : asLLVMConstantProperties amountProps = typedAmount
  cases typedAmount with
  | mk amountValue => cases amountValue with
    | float _ | dense _ | string _ =>
      simp [isIntegralConstant, hTypedAmount] at hAmount
    | integer amountAttr =>
      have hInterpAmountTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties amountProps) #[IntegerType.mk w signedness]
          #[] #[amount] := hInterpAmount
      rw [hTypedAmount] at hInterpAmountTyped
      obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmountTyped
      rintro shiftProps shifted hShiftNSW hShifted
      obtain rfl := (shl_iff _ shiftProps _ _ _).mp hShifted
      rintro multiplierProps multiplier hMultiplier hInterpMultiplier
      generalize hTypedMultiplier :
          asLLVMConstantProperties multiplierProps = typedMultiplier
      cases typedMultiplier with
      | mk multiplierValue => cases multiplierValue with
        | float _ | dense _ | string _ =>
          simp [isIntegralConstant, hTypedMultiplier] at hMultiplier
        | integer multiplierAttr =>
          have hInterpMultiplierTyped : InterpretsTo (.llvm .mlir__constant)
              (asLLVMConstantProperties multiplierProps) #[IntegerType.mk w signedness]
              #[] #[multiplier] := hInterpMultiplier
          rw [hTypedMultiplier] at hInterpMultiplierTyped
          obtain rfl := (constant_iff _ multiplierAttr _).mp hInterpMultiplierTyped
          rintro mulProps source hMulNSW hSource hChecks
          obtain rfl := (mul_iff _ _ _ _ _).mp hSource
          have hAmountValue :
              amountProps.value = LLVMConstantValue.integer amountAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedAmount
          have hMultiplierValue :
              multiplierProps.value = LLVMConstantValue.integer multiplierAttr := by
            simpa [asLLVMConstantProperties] using
              congrArg (fun p : LLVMConstantProperties => p.value) hTypedMultiplier
          have hRange : (BitVec.ofInt w amountAttr.value).toNat < w := by
            simpa [shiftedConstantsValidForNSW, isInRangeAmount,
              shiftedConstantNotSignedMin, hAmountValue, hMultiplierValue,
              asLLVMConstantProperties, IsTypeAttr.cast?_of] using
              (Bool.and_eq_true_iff.mp hChecks).1
          have hFoldedNotMin :
              BitVec.ofInt w multiplierAttr.value <<<
                  BitVec.ofInt w amountAttr.value ≠ BitVec.intMin w := by
            simpa [shiftedConstantsValidForNSW, shiftedConstantNotSignedMin,
              isInRangeAmount, hAmountValue, hMultiplierValue,
              asLLVMConstantProperties, IsTypeAttr.cast?_of] using
              (Bool.and_eq_true_iff.mp hChecks).2
          rw [hShiftNSW, hMulNSW]
          simp [shiftedConstantProperties, hTypedAmount, hTypedMultiplier,
            IsTypeAttr.cast?_of]
          let folded := BitVec.ofInt w multiplierAttr.value <<<
            BitVec.ofInt w amountAttr.value
          have hFoldedConstant : folded = BitVec.ofInt w
              (IntegerAttr.normalizeValue
                { bitwidth := w, signedness := signedness }
                (folded.toNat : Int)) := by
            calc
              folded = BitVec.ofInt w (folded.toNat : Int) := by
                rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              _ = BitVec.ofInt w
                    (IntegerAttr.normalizeValue
                      { bitwidth := w, signedness := signedness }
                      (folded.toNat : Int)) :=
                (ofInt_normalizeValue
                  { bitwidth := w, signedness := signedness }
                  (folded.toNat : Int)).symm
          refine ⟨.int w (.val folded), ?_, ?_⟩
          · apply (constant_iff _ _ _).mpr
            simpa [folded, IntegerAttr.ofInt] using congrArg
              (fun z => RuntimeValue.int w (.val z)) hFoldedConstant
          refine ⟨.int w (LLVM.Int.mul x (.val folded) true false), ?_, ?_⟩
          · exact (mul_iff _ _ _ _ _).mpr rfl
          refine ⟨rfl, ?_⟩
          simpa only [folded, LLVM.Int.cast_self] using
            (mul_shift_constant_nsw_refines w x
              (BitVec.ofInt w multiplierAttr.value)
              (BitVec.ofInt w amountAttr.value) hRange hFoldedNotMin
              shiftProps.nuw mulProps.nuw)

end Veir.Passes.InstCombineLLVM.MulShiftConstant
