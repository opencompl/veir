module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorOrSelf

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def allOnesProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-1) intType))

private def xorOrSelfPattern (rootCommuted orCommuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let or ← if orCommuted then
        MatchProg.operation (.llvm .or) #[y, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[x, y] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[or.res[0]!, y] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[y, or.res[0]!] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let cp ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
      let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
      let xp ← CreateProg.property (.llvm .xor) ()
      let notY ← CreateProg.operation (.llvm .xor) #[y, minusOne.res[0]!] #[ty] xp
      let ap ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[x, notY.res[0]!] #[ty] ap)
    (fun result => result.res[0]!)

private theorem xorOrSelfPattern_valid (rootCommuted orCommuted : Bool) :
    Pattern.Valid (xorOrSelfPattern rootCommuted orCommuted) := by
  cases rootCommuted <;> cases orCommuted <;>
    simp only [xorOrSelfPattern, Bool.false_eq_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ x y
    rintro orProps or hOr
    obtain rfl := (or_iff _ _ _ _ _).mp hOr
    rintro ⟨⟩ source hSource
    obtain rfl := (xor_iff _ _ _ _).mp hSource
    simp [allOnesProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue { bitwidth := w, signedness := s } (-1)).symm
    refine ⟨.int w (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))),
      (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int w (LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1))))),
      (and_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
      (xor_self_or_refines_and_not w x y orProps.disjoint)

/-- Scalar semantic specialization of InstCombineAndOrXor.cpp:5680-5681:
    `Y xor (X or Y) -> X and ~Y`. The source one-use guard is profitability-only. -/
public def xorOrSelf : Pattern OpCode := xorOrSelfPattern false false

public theorem xorOrSelf_valid : Pattern.Valid xorOrSelf :=
  xorOrSelfPattern_valid false false

/-- Variant with the inner `or` operands commuted. -/
public def xorCommutedOrSelf : Pattern OpCode := xorOrSelfPattern false true

public theorem xorCommutedOrSelf_valid : Pattern.Valid xorCommutedOrSelf :=
  xorOrSelfPattern_valid false true

/-- Variant with the root `xor` operands commuted. -/
public def orSelfXor : Pattern OpCode := xorOrSelfPattern true false

public theorem orSelfXor_valid : Pattern.Valid orSelfXor :=
  xorOrSelfPattern_valid true false

/-- Variant with root and inner commutation. -/
public def commutedOrSelfXor : Pattern OpCode := xorOrSelfPattern true true

public theorem commutedOrSelfXor_valid : Pattern.Valid commutedOrSelfXor :=
  xorOrSelfPattern_valid true true

end Veir.Passes.InstCombineLLVM.XorOrSelf
