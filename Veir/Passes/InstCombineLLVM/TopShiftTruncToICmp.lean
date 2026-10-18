module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

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

private def zeroProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

private inductive ShiftKind | lshr | ashr

private def ShiftKind.op : ShiftKind → OpCode
  | .lshr => .llvm .lshr
  | .ashr => .llvm .ashr

private def pattern (kind : ShiftKind) : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let x ← MatchProg.value wideTy
      let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[wideTy]
        (fun _ => true)
      MatchProg.matchNative (wideTy, amount.properties) isTopBitShiftAmount
      let shifted ← MatchProg.operation kind.op #[x, amount.res[0]!] #[wideTy]
        (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[shifted.res[0]!] #[boolTy]
        (fun _ => true)
      return (wideTy, boolTy, x))
    (fun (wideTy, boolTy, x) => do
      let zeroProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        wideTy zeroProperty
      let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] zeroProps
      let cmpProps ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .slt)
      CreateProg.operation (.llvm .icmp) #[x, zero.res[0]!] #[boolTy] cmpProps)
    (fun result => result.res[0]!)

private theorem pattern_valid (kind : ShiftKind) : Pattern.Valid (pattern kind) := by
  cases kind <;> simp only [pattern, ShiftKind.op] <;> unfoldPuddleBuilder
  · constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;>
        simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
          MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
          HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
          HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
          HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
          MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
          CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    rintro ⟨w, signedness⟩ boolType ⟨boolW, boolSignedness⟩ hBool hBoolW
    subst boolType; change boolW = 1 at hBoolW; subst boolW
    rintro x hX
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
    rintro ⟨constantValue⟩ amount hInterpAmount
    cases constantValue with
    | float _ | dense _ | string _ =>
      simp [isTopBitShiftAmount, asLLVMConstantProperties]
    | integer amountAttr =>
      obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmount
      rintro shiftProps shifted hShifted
      obtain rfl := (lshr_iff _ _ _ _ _).mp hShifted
      rintro truncProps source hSource hAmount
      obtain ⟨h1w, rfl⟩ := (trunc_iff w 1 truncProps _ source).mp hSource
      have hTop : BitVec.ofInt w amountAttr.value =
          BitVec.ofInt w (Int.ofNat (w - 1)) := by
        simpa [isTopBitShiftAmount, asLLVMConstantProperties, IsTypeAttr.cast?_of]
          using hAmount
      rw [hTop]
      simp [zeroProperty, IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 0).symm
      refine ⟨.int 1 (LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .slt),
        (icmp_iff _ (IcmpProperties.mk .slt) _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [show BitVec.ofNat w (w - 1) =
        BitVec.ofInt w (Int.ofNat (w - 1)) by rfl]
      simpa only [LLVM.Int.cast_self] using
        trunc_lshr_top_refines_icmp_slt h1w x shiftProps.exact
          truncProps.nsw truncProps.nuw
  · constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;>
        simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
          MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
          HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
          HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
          HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
          MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
          CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    rintro ⟨w, signedness⟩ boolType ⟨boolW, boolSignedness⟩ hBool hBoolW
    subst boolType; change boolW = 1 at hBoolW; subst boolW
    rintro x hX
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
    rintro ⟨constantValue⟩ amount hInterpAmount
    cases constantValue with
    | float _ | dense _ | string _ =>
      simp [isTopBitShiftAmount, asLLVMConstantProperties]
    | integer amountAttr =>
      obtain rfl := (constant_iff _ amountAttr _).mp hInterpAmount
      rintro shiftProps shifted hShifted
      obtain rfl := (ashr_iff _ _ _ _ _).mp hShifted
      rintro truncProps source hSource hAmount
      obtain ⟨h1w, rfl⟩ := (trunc_iff w 1 truncProps _ source).mp hSource
      have hTop : BitVec.ofInt w amountAttr.value =
          BitVec.ofInt w (Int.ofNat (w - 1)) := by
        simpa [isTopBitShiftAmount, asLLVMConstantProperties, IsTypeAttr.cast?_of]
          using hAmount
      rw [hTop]
      simp [zeroProperty, IsTypeAttr.cast?_of]
      refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
      · apply (constant_iff _ _ _).mpr
        simpa [IntegerAttr.ofInt] using congrArg
          (fun z => RuntimeValue.int w (.val z))
          (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 0).symm
      refine ⟨.int 1 (LLVM.Int.icmp x (.val (BitVec.ofInt w 0)) .slt),
        (icmp_iff _ (IcmpProperties.mk .slt) _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      rw [show BitVec.ofNat w (w - 1) =
        BitVec.ofInt w (Int.ofNat (w - 1)) by rfl]
      simpa only [LLVM.Int.cast_self] using
        trunc_ashr_top_refines_icmp_slt h1w x shiftProps.exact
          truncProps.nsw truncProps.nuw

/-- InstCombineCasts.cpp:1136-1141, logical-right-shift variant, for arbitrary scalar
    integer widths: `trunc (lshr X, BW-1) to i1` becomes `icmp slt X, 0`. -/
public def truncLShrTopToICmpSlt : Pattern OpCode := pattern .lshr

public theorem truncLShrTopToICmpSlt_valid : Pattern.Valid truncLShrTopToICmpSlt :=
  pattern_valid .lshr

/-- InstCombineCasts.cpp:1136-1141, arithmetic-right-shift variant, for arbitrary scalar
    integer widths: `trunc (ashr X, BW-1) to i1` becomes `icmp slt X, 0`. -/
public def truncAShrTopToICmpSlt : Pattern OpCode := pattern .ashr

public theorem truncAShrTopToICmpSlt_valid : Pattern.Valid truncAShrTopToICmpSlt :=
  pattern_valid .ashr

end Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp

#print axioms Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp.truncLShrTopToICmpSlt_valid
#print axioms Veir.Passes.InstCombineLLVM.TopShiftTruncToICmp.truncAShrTopToICmpSlt_valid
