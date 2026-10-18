module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorAndSelf

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

private def xorAndSelfPattern (rootCommuted andCommuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let and ← if andCommuted then
        MatchProg.operation (.llvm .and) #[y, x] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .and) #[x, y] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[and.res[0]!, y] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[y, and.res[0]!] #[ty] (fun _ => true)
      return (ty, x, y))
    (fun (ty, x, y) => do
      let cp ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
      let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
      let xp ← CreateProg.property (.llvm .xor) ()
      let notX ← CreateProg.operation (.llvm .xor) #[x, minusOne.res[0]!] #[ty] xp
      let ap ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[notX.res[0]!, y] #[ty] ap)
    (fun result => result.res[0]!)

private theorem xorAndSelfPattern_valid (rootCommuted andCommuted : Bool) :
    Pattern.Valid (xorAndSelfPattern rootCommuted andCommuted) := by
  cases rootCommuted <;> cases andCommuted <;>
    simp only [xorAndSelfPattern, Bool.false_eq_true, ite_false, ite_true] <;>
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
    rintro ⟨⟩ sourceAnd hAnd
    obtain rfl := (and_iff _ _ _ _).mp hAnd
    rintro ⟨⟩ source hSource
    obtain rfl := (xor_iff _ _ _ _).mp hSource
    simp [allOnesProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue { bitwidth := w, signedness := s } (-1)).symm
    refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))),
      (xor_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨.int w (LLVM.Int.and (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) y),
      (and_iff _ _ _ _).mpr rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    simpa only [LLVM.Int.cast_self, llvm_and_comm, llvm_xor_comm] using
      (xor_self_and_refines_not_and w x y)

/-- Scalar semantic specialization of InstCombineAndOrXor.cpp:5689-5690:
    `Y xor (X and Y) -> ~X and Y`. The source one-use and nonconstant guards are
    profitability and canonicality conditions. -/
public def xorAndSelf : Pattern OpCode := xorAndSelfPattern false false

public theorem xorAndSelf_valid : Pattern.Valid xorAndSelf :=
  xorAndSelfPattern_valid false false

/-- Variant with the inner `and` operands commuted. -/
public def xorCommutedAndSelf : Pattern OpCode := xorAndSelfPattern false true

public theorem xorCommutedAndSelf_valid : Pattern.Valid xorCommutedAndSelf :=
  xorAndSelfPattern_valid false true

/-- Variant with the root `xor` operands commuted. -/
public def andSelfXor : Pattern OpCode := xorAndSelfPattern true false

public theorem andSelfXor_valid : Pattern.Valid andSelfXor :=
  xorAndSelfPattern_valid true false

/-- Variant with root and inner commutation. -/
public def commutedAndSelfXor : Pattern OpCode := xorAndSelfPattern true true

public theorem commutedAndSelfXor_valid : Pattern.Valid commutedAndSelfXor :=
  xorAndSelfPattern_valid true true

end Veir.Passes.InstCombineLLVM.XorAndSelf
