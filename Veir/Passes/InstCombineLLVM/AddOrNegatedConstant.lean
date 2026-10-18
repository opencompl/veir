module

public import Veir.Passes.InstCombineLLVM.ProofTactics
public import Veir.Passes.InstCombineLLVM.ArithmeticBitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.AddOrNegatedConstant

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

private def areNegatedConstants
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant) ×
      propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, innerProps, outerProps) := input
  match type.cast? IntegerType, (asLLVMConstantProperties innerProps).value,
      (asLLVMConstantProperties outerProps).value with
  | some intType, .integer inner, .integer outer =>
      decide (BitVec.ofInt intType.bitwidth inner.value =
        -(BitVec.ofInt intType.bitwidth outer.value))
  | _, _, _ => false

private def addOrNegatedConstantPattern (commuted : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let innerConstant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    let either ← if commuted then
      MatchProg.operation (.llvm .or) #[innerConstant.res[0]!, x] #[ty] (fun _ => true)
    else
      MatchProg.operation (.llvm .or) #[x, innerConstant.res[0]!] #[ty] (fun _ => true)
    let outerConstant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      isIntegralConstant
    MatchProg.matchNative (ty, innerConstant.properties, outerConstant.properties)
      areNegatedConstants
    let _ ← MatchProg.root (.llvm .add) #[either.res[0]!, outerConstant.res[0]!] #[ty]
      (fun _ => true)
    return (ty, either.res[0]!, innerConstant.res[0]!))
  (fun (ty, either, innerConstant) => do
    let xp ← CreateProg.property (.llvm .xor) ()
    CreateProg.operation (.llvm .xor) #[either, innerConstant] #[ty] xp)
  (fun result => result.res[0]!)

set_option linter.tacticCheckInstances false in
private theorem addOrNegatedConstantPattern_valid (commuted : Bool) :
    Pattern.Valid (addOrNegatedConstantPattern commuted) := by
  cases commuted <;> simp only [addOrNegatedConstantPattern, Bool.false_eq_true, ite_false,
      ite_true] <;> unfoldPuddleBuilder
  all_goals
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
    rintro innerProps innerConstant hInner hInterpInner
    generalize hTypedInner : asLLVMConstantProperties innerProps = typedInner
    cases typedInner with
    | mk innerValue => cases innerValue with
      | float _ | dense _ | string _ =>
        simp [isIntegralConstant, hTypedInner] at hInner
      | integer innerAttr =>
        have hInterpInnerTyped : InterpretsTo (.llvm .mlir__constant)
            (asLLVMConstantProperties innerProps) #[IntegerType.mk w signedness]
            #[] #[innerConstant] := hInterpInner
        rw [hTypedInner] at hInterpInnerTyped
        obtain rfl := (constant_iff _ innerAttr _).mp hInterpInnerTyped
        rintro orProps either hEither
        obtain rfl := (or_iff _ _ _ _ _).mp hEither
        rintro outerProps outerConstant hOuter hInterpOuter
        generalize hTypedOuter : asLLVMConstantProperties outerProps = typedOuter
        cases typedOuter with
        | mk outerValue => cases outerValue with
          | float _ | dense _ | string _ =>
            simp [isIntegralConstant, hTypedOuter] at hOuter
          | integer outerAttr =>
            have hInterpOuterTyped : InterpretsTo (.llvm .mlir__constant)
                (asLLVMConstantProperties outerProps) #[IntegerType.mk w signedness]
                #[] #[outerConstant] := hInterpOuter
            rw [hTypedOuter] at hInterpOuterTyped
            obtain rfl := (constant_iff _ outerAttr _).mp hInterpOuterTyped
            rintro addProps source hSource hNegated
            obtain rfl := (add_iff _ _ _ _ _).mp hSource
            have hInnerValue :
                innerProps.value = LLVMConstantValue.integer innerAttr := by
              simpa [asLLVMConstantProperties] using
                congrArg (fun p : LLVMConstantProperties => p.value) hTypedInner
            have hOuterValue :
                outerProps.value = LLVMConstantValue.integer outerAttr := by
              simpa [asLLVMConstantProperties] using
                congrArg (fun p : LLVMConstantProperties => p.value) hTypedOuter
            have hNeg : BitVec.ofInt w innerAttr.value =
                -(BitVec.ofInt w outerAttr.value) := by
              simpa [areNegatedConstants, hInnerValue, hOuterValue,
                asLLVMConstantProperties, IsTypeAttr.cast?_of] using hNegated
            refine ⟨.int w (LLVM.Int.xor
              (LLVM.Int.or x (.val (BitVec.ofInt w innerAttr.value)) orProps.disjoint)
              (.val (BitVec.ofInt w innerAttr.value))), ?_, ?_⟩
            · apply (xor_iff _ _ _ _).mpr
              first | rfl | rw [llvm_or_comm]
            refine ⟨rfl, ?_⟩
            first
            | simpa only [LLVM.Int.cast_self] using
                (add_or_negated_constant_refines_xor w x
                  (BitVec.ofInt w outerAttr.value) (BitVec.ofInt w innerAttr.value)
                  hNeg orProps.disjoint addProps.nsw addProps.nuw)
            | simpa only [LLVM.Int.cast_self, llvm_or_comm] using
                (add_or_negated_constant_refines_xor w x
                  (BitVec.ofInt w outerAttr.value) (BitVec.ofInt w innerAttr.value)
                  hNeg orProps.disjoint addProps.nsw addProps.nuw)

/-- InstCombineAddSub.cpp:932-936, canonical `X | C2` operand order. -/
public def addOrNegatedConstant : Pattern OpCode := addOrNegatedConstantPattern false
public theorem addOrNegatedConstant_valid : Pattern.Valid addOrNegatedConstant :=
  addOrNegatedConstantPattern_valid false

/-- Source-supported commuted `C2 | X` operand order. -/
public def addCommutedOrNegatedConstant : Pattern OpCode :=
  addOrNegatedConstantPattern true
public theorem addCommutedOrNegatedConstant_valid :
    Pattern.Valid addCommutedOrNegatedConstant :=
  addOrNegatedConstantPattern_valid true

end Veir.Passes.InstCombineLLVM.AddOrNegatedConstant
