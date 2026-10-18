module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.NegateRightShift

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

private def isTopBitShiftAmount
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, props) := input
  match type.cast? IntegerType, (asLLVMConstantProperties props).value with
  | some intType, .integer attr =>
      BitVec.ofInt intType.bitwidth attr.value ==
        BitVec.ofInt intType.bitwidth (Int.ofNat (intType.bitwidth - 1))
  | _, _ => false

private def copyAShrExact
    (props : propertiesOf (OpCode.llvm .ashr)) :
    Option (propertiesOf (OpCode.llvm .lshr)) :=
  some { exact := props.exact }

private def copyLShrExact
    (props : propertiesOf (OpCode.llvm .lshr)) :
    Option (propertiesOf (OpCode.llvm .ashr)) :=
  some { exact := props.exact }

/-- Scalar specialization of InstCombineNegator.cpp:166-179:
    `-(ashr x, W-1) -> lshr x, W-1`, preserving `exact`. -/
public def negateAShrSignBit : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] (fun _ => true)
      MatchProg.matchNative (ty, amount.properties) isTopBitShiftAmount
      let shifted ← MatchProg.operation (.llvm .ashr) #[x, amount.res[0]!] #[ty]
        (fun _ => true)
      let zero ← matchIntConstant ty 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, shifted.res[0]!] #[ty] (fun _ => true)
      return (ty, x, amount.res[0]!, shifted.properties))
    (fun (ty, x, amount, shiftProps) => do
      let copiedProps ← CreateProg.applyNative
        (Inputs := Handle OpCode (.prop (.llvm .ashr)))
        (Outputs := Handle OpCode (.prop (.llvm .lshr))) shiftProps copyAShrExact
      CreateProg.operation (.llvm .lshr) #[x, amount] #[ty] copiedProps)
    (fun result => result.res[0]!)

public theorem negateAShrSignBit_valid : Pattern.Valid negateAShrSignBit := by
  simp only [negateAShrSignBit, matchIntConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings,
        copyAShrExact]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ value hValue
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hValue
  rintro ⟨constantValue⟩ amount hInterpAmount
  cases constantValue with
  | float _ | dense _ | string _ =>
    simp [isTopBitShiftAmount, asLLVMConstantProperties]
  | integer amountAttr =>
    obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmount
    rintro shiftProps shifted hShifted
    obtain rfl := (ashr_iff _ _ _ _ _).mp hShifted
    rintro ⟨zeroValue⟩ zero hZero hInterpZero
    cases zeroValue with
    | float _ | dense _ | string _ => simp at hZero
    | integer zeroAttr =>
      have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
      obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
      rintro negProps source hSource hAmount
      obtain rfl := (sub_iff _ _ _ _ _).mp hSource
      have hTop :
          BitVec.ofInt w amountAttr.value =
            BitVec.ofInt w (Int.ofNat (w - 1)) := by
        simpa [isTopBitShiftAmount, asLLVMConstantProperties, IsTypeAttr.cast?_of]
          using hAmount
      rw [hZeroValue, hTop]
      simp only [copyAShrExact]
      refine ⟨.int w (LLVM.Int.lshr x
        (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) shiftProps.exact), ?_, ?_⟩
      · exact (lshr_iff _ _ _ _ _).mpr rfl
      change ∃ h : w = w,
        (LLVM.Int.sub (.val (BitVec.ofInt w 0))
          (LLVM.Int.ashr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) shiftProps.exact)
          negProps.nsw negProps.nuw).cast h ⊒
          LLVM.Int.lshr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) shiftProps.exact
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (isRefinedBy_trans
          (sub_flags_refine w (.val (BitVec.ofInt w 0))
            (LLVM.Int.ashr x (.val (BitVec.ofInt w (Int.ofNat (w - 1))))
              shiftProps.exact) negProps.nsw negProps.nuw)
          (by rw [neg_ashr_top]; exact isRefinedBy_refl _))

/-- Mirror specialization: `-(lshr x, W-1) -> ashr x, W-1`, preserving `exact`. -/
public def negateLShrSignBit : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] (fun _ => true)
      MatchProg.matchNative (ty, amount.properties) isTopBitShiftAmount
      let shifted ← MatchProg.operation (.llvm .lshr) #[x, amount.res[0]!] #[ty]
        (fun _ => true)
      let zero ← matchIntConstant ty 0
      let _ ← MatchProg.root (.llvm .sub) #[zero, shifted.res[0]!] #[ty] (fun _ => true)
      return (ty, x, amount.res[0]!, shifted.properties))
    (fun (ty, x, amount, shiftProps) => do
      let copiedProps ← CreateProg.applyNative
        (Inputs := Handle OpCode (.prop (.llvm .lshr)))
        (Outputs := Handle OpCode (.prop (.llvm .ashr))) shiftProps copyLShrExact
      CreateProg.operation (.llvm .ashr) #[x, amount] #[ty] copiedProps)
    (fun result => result.res[0]!)

public theorem negateLShrSignBit_valid : Pattern.Valid negateLShrSignBit := by
  simp only [negateLShrSignBit, matchIntConstant]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings,
        copyLShrExact]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ value hValue
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hValue
  rintro ⟨constantValue⟩ amount hInterpAmount
  cases constantValue with
  | float _ | dense _ | string _ =>
    simp [isTopBitShiftAmount, asLLVMConstantProperties]
  | integer amountAttr =>
    obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmount
    rintro shiftProps shifted hShifted
    obtain rfl := (lshr_iff _ _ _ _ _).mp hShifted
    rintro ⟨zeroValue⟩ zero hZero hInterpZero
    cases zeroValue with
    | float _ | dense _ | string _ => simp at hZero
    | integer zeroAttr =>
      have hZeroValue : zeroAttr.value = 0 := of_decide_eq_true hZero
      obtain rfl := (constant_iff _ zeroAttr _).mp hInterpZero
      rintro negProps source hSource hAmount
      obtain rfl := (sub_iff _ _ _ _ _).mp hSource
      have hTop :
          BitVec.ofInt w amountAttr.value =
            BitVec.ofInt w (Int.ofNat (w - 1)) := by
        simpa [isTopBitShiftAmount, asLLVMConstantProperties, IsTypeAttr.cast?_of]
          using hAmount
      rw [hZeroValue, hTop]
      simp only [copyLShrExact]
      refine ⟨.int w (LLVM.Int.ashr x
        (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) shiftProps.exact), ?_, ?_⟩
      · exact (ashr_iff _ _ _ _ _).mpr rfl
      change ∃ h : w = w,
        (LLVM.Int.sub (.val (BitVec.ofInt w 0))
          (LLVM.Int.lshr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) shiftProps.exact)
          negProps.nsw negProps.nuw).cast h ⊒
          LLVM.Int.ashr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) shiftProps.exact
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        (isRefinedBy_trans
          (sub_flags_refine w (.val (BitVec.ofInt w 0))
            (LLVM.Int.lshr x (.val (BitVec.ofInt w (Int.ofNat (w - 1))))
              shiftProps.exact) negProps.nsw negProps.nuw)
          (by rw [neg_lshr_top]; exact isRefinedBy_refl _))

end Veir.Passes.InstCombineLLVM.NegateRightShift
