module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def oneConstantProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 1 intType))

private def zeroConstantProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))

private def pattern (commuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let x ← MatchProg.value wideTy
      let amount ← MatchProg.operation (.llvm .mlir__constant) #[] #[wideTy]
        isIntegralConstant
      let shifted ← MatchProg.operation (.llvm .lshr) #[x, amount.res[0]!] #[wideTy]
        (fun _ => true)
      let joined ← MatchProg.operation (.llvm .or)
        (match commuted with
        | false => #[shifted.res[0]!, x]
        | true => #[x, shifted.res[0]!]) #[wideTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[joined.res[0]!] #[boolTy]
        (fun _ => true)
      return (wideTy, boolTy, x, amount.res[0]!))
    (fun (wideTy, boolTy, x, amount) => do
      let oneProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        wideTy oneConstantProperty
      let one ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] oneProps
      let zeroProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        wideTy zeroConstantProperty
      let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[wideTy] zeroProps
      let shlProps ← CreateProg.property (.llvm .shl) default
      let shiftedMask ← CreateProg.operation (.llvm .shl) #[one.res[0]!, amount]
        #[wideTy] shlProps
      let orProps ← CreateProg.property (.llvm .or) default
      let mask ← CreateProg.operation (.llvm .or) #[shiftedMask.res[0]!, one.res[0]!]
        #[wideTy] orProps
      let andProps ← CreateProg.property (.llvm .and) ()
      let masked ← CreateProg.operation (.llvm .and) #[x, mask.res[0]!] #[wideTy]
        andProps
      let cmpProps ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
      CreateProg.operation (.llvm .icmp) #[masked.res[0]!, zero.res[0]!] #[boolTy]
        cmpProps)
    (fun result => result.res[0]!)

private theorem pattern_valid (commuted : Bool) : Pattern.Valid (pattern commuted) := by
  cases commuted <;> simp only [pattern] <;> unfoldPuddleBuilder
  all_goals
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
          CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    rintro ⟨w, signedness⟩ boolType ⟨boolW, boolSignedness⟩ hBool hBoolW
    subst boolType; change boolW = 1 at hBoolW; subst boolW
    rintro x hX
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
    rintro constantProps amount hConstant hInterpAmount
    generalize hTyped : asLLVMConstantProperties constantProps = typedProps
    cases typedProps with
    | mk constantValue => cases constantValue with
      | float _ | dense _ | string _ => simp [isIntegralConstant, hTyped] at hConstant
      | integer amountAttr =>
        have hInterpTyped : InterpretsTo (.llvm .mlir__constant)
            (asLLVMConstantProperties constantProps)
            #[IntegerType.mk w signedness] #[] #[amount] := hInterpAmount
        rw [hTyped] at hInterpTyped
        obtain rfl := (constant_iff _ amountAttr _).mp hInterpTyped
        rintro shiftProps shifted hShifted
        obtain rfl := (lshr_iff _ _ _ _ _).mp hShifted
        rintro orProps joined hJoined
        obtain rfl := (or_iff _ orProps _ _ _).mp hJoined
        rintro truncProps source hSource
        obtain ⟨h1w, rfl⟩ := (trunc_iff w 1 truncProps _ source).mp hSource
        simp [oneConstantProperty, zeroConstantProperty, IsTypeAttr.cast?_of]
        refine ⟨.int w (.val (BitVec.ofInt w 1)), ?_, ?_⟩
        · apply (constant_iff _ _ _).mpr
          simpa [IntegerAttr.ofInt] using congrArg
            (fun z => RuntimeValue.int w (.val z))
            (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 1).symm
        refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
        · apply (constant_iff _ _ _).mpr
          simpa [IntegerAttr.ofInt] using congrArg
            (fun z => RuntimeValue.int w (.val z))
            (ofInt_normalizeValue { bitwidth := w, signedness := signedness } 0).symm
        refine ⟨.int w (LLVM.Int.shl (.val (BitVec.ofInt w 1))
          (.val (BitVec.ofInt w amountAttr.value)) false false), ?_, ?_⟩
        · exact (shl_iff _ default _ _ _).mpr rfl
        refine ⟨.int w (LLVM.Int.or (LLVM.Int.shl (.val (BitVec.ofInt w 1))
          (.val (BitVec.ofInt w amountAttr.value)) false false)
          (.val (BitVec.ofInt w 1)) false), ?_, ?_⟩
        · exact (or_iff _ default _ _ _).mpr rfl
        refine ⟨.int w (LLVM.Int.and x (LLVM.Int.or
          (LLVM.Int.shl (.val (BitVec.ofInt w 1))
            (.val (BitVec.ofInt w amountAttr.value)) false false)
          (.val (BitVec.ofInt w 1)) false)), ?_, ?_⟩
        · exact (and_iff _ _ _ _).mpr rfl
        refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.and x (LLVM.Int.or
          (LLVM.Int.shl (.val (BitVec.ofInt w 1))
            (.val (BitVec.ofInt w amountAttr.value)) false false)
          (.val (BitVec.ofInt w 1)) false))
          (.val (BitVec.ofInt w 0)) .ne), ?_, ?_⟩
        · exact (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl
        refine ⟨rfl, ?_⟩
        rw [show BitVec.ofInt w 1 = (1 : BitVec w) by rfl,
          show BitVec.ofInt w 0 = (0 : BitVec w) by rfl]
        first
        | simpa only [LLVM.Int.cast_self] using
            trunc_or_lshr_refines_bit_test h1w x
              (BitVec.ofInt w amountAttr.value) shiftProps.exact
              orProps.disjoint truncProps.nsw truncProps.nuw
        | rw [llvm_or_comm x
              (LLVM.Int.lshr x (.val (BitVec.ofInt w amountAttr.value))
                shiftProps.exact) orProps.disjoint]
          simpa only [LLVM.Int.cast_self] using
            trunc_or_lshr_refines_bit_test h1w x
              (BitVec.ofInt w amountAttr.value) shiftProps.exact
              orProps.disjoint truncProps.nsw truncProps.nuw

/-- InstCombineCasts.cpp:1153-1162, `lshr` in the left operand of the commutative
    `or`, for arbitrary scalar integer widths and arbitrary immediate amounts. -/
public def orLShrTruncToBitTest : Pattern OpCode := pattern false

public theorem orLShrTruncToBitTest_valid : Pattern.Valid orLShrTruncToBitTest :=
  pattern_valid false

/-- Operand-swapped form admitted by LLVM's `m_c_Or` matcher. -/
public def orLShrTruncToBitTestCommuted : Pattern OpCode := pattern true

public theorem orLShrTruncToBitTestCommuted_valid :
    Pattern.Valid orLShrTruncToBitTestCommuted := pattern_valid true

end Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest

#print axioms Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest.orLShrTruncToBitTest_valid
#print axioms Veir.Passes.InstCombineLLVM.OrLShrTruncToBitTest.orLShrTruncToBitTestCommuted_valid
