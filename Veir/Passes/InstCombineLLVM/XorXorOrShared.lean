module

public import Veir.Passes.InstCombineLLVM.BitwiseSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.XorXorOrShared

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

private def xorXorOrSharedPattern
    (sharedRight rootCommuted orCommuted : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let c ← MatchProg.value ty
      let innerXor ← MatchProg.operation (.llvm .xor) #[a, b] #[ty] (fun _ => true)
      let shared := if sharedRight then b else a
      let other := if sharedRight then a else b
      let innerOr ← if orCommuted then
        MatchProg.operation (.llvm .or) #[c, shared] #[ty] (fun _ => true)
      else
        MatchProg.operation (.llvm .or) #[shared, c] #[ty] (fun _ => true)
      let _ ← if rootCommuted then
        MatchProg.root (.llvm .xor) #[innerOr.res[0]!, innerXor.res[0]!] #[ty] (fun _ => true)
      else
        MatchProg.root (.llvm .xor) #[innerXor.res[0]!, innerOr.res[0]!] #[ty] (fun _ => true)
      return (ty, shared, other, c))
    (fun (ty, shared, other, c) => do
      let cp ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
      let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
      let xp ← CreateProg.property (.llvm .xor) ()
      let notShared ← CreateProg.operation (.llvm .xor) #[shared, minusOne.res[0]!] #[ty] xp
      let ap ← CreateProg.property (.llvm .and) ()
      let masked ← CreateProg.operation (.llvm .and) #[notShared.res[0]!, c] #[ty] ap
      let xp' ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[masked.res[0]!, other] #[ty] xp')
    (fun result => result.res[0]!)

set_option maxHeartbeats 1000000 in
private theorem xorXorOrSharedPattern_valid
    (sharedRight rootCommuted orCommuted : Bool) :
    Pattern.Valid (xorXorOrSharedPattern sharedRight rootCommuted orCommuted) := by
  cases sharedRight <;> cases rootCommuted <;> cases orCommuted <;>
    simp only [xorXorOrSharedPattern, Bool.false_eq_true, ite_false, ite_true] <;>
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
    rintro ⟨w, s⟩ a b c
    rintro ⟨⟩ sourceXor hSourceXor
    obtain rfl := (xor_iff _ _ _ _).mp hSourceXor
    rintro orProps sourceOr hSourceOr
    obtain rfl := (or_iff _ _ _ _ _).mp hSourceOr
    rintro ⟨⟩ source hSource
    obtain rfl := (xor_iff _ _ _ _).mp hSource
    simp [allOnesProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue { bitwidth := w, signedness := s } (-1)).symm
    first
    | refine ⟨.int w (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) c),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor
          (LLVM.Int.and (LLVM.Int.xor a (.val (BitVec.ofInt w (-1)))) c) b),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (xor_xor_or_shared_refines w a b c orProps.disjoint)
    | refine ⟨.int w (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.and (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) c),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int w (LLVM.Int.xor
          (LLVM.Int.and (LLVM.Int.xor b (.val (BitVec.ofInt w (-1)))) c) a),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self, llvm_or_comm, llvm_xor_comm] using
        (xor_xor_or_shared_refines w b a c orProps.disjoint)

/-- Scalar specialization of InstCombineAndOrXor.cpp:5702-5705:
    `(A xor B) xor (A or C) -> (~A and C) xor B`. The source one-use conditions
    are profitability guards. -/
public def xorXorOrShared : Pattern OpCode := xorXorOrSharedPattern false false false

public theorem xorXorOrShared_valid : Pattern.Valid xorXorOrShared :=
  xorXorOrSharedPattern_valid false false false

/-- Variant with the source `or` operands commuted. -/
public def xorXorCommutedOrShared : Pattern OpCode := xorXorOrSharedPattern false false true

public theorem xorXorCommutedOrShared_valid : Pattern.Valid xorXorCommutedOrShared :=
  xorXorOrSharedPattern_valid false false true

/-- Variant with the root `xor` operands commuted. -/
public def xorOrSharedXor : Pattern OpCode := xorXorOrSharedPattern false true false

public theorem xorOrSharedXor_valid : Pattern.Valid xorOrSharedXor :=
  xorXorOrSharedPattern_valid false true false

/-- Variant with source root and `or` operands commuted. -/
public def xorCommutedOrSharedXor : Pattern OpCode := xorXorOrSharedPattern false true true

public theorem xorCommutedOrSharedXor_valid : Pattern.Valid xorCommutedOrSharedXor :=
  xorXorOrSharedPattern_valid false true true

/-- Source's second shared-operand branch: `(A xor B) xor (B or C)`. -/
public def xorXorOrSharedRight : Pattern OpCode :=
  xorXorOrSharedPattern true false false

public theorem xorXorOrSharedRight_valid : Pattern.Valid xorXorOrSharedRight :=
  xorXorOrSharedPattern_valid true false false

/-- Second shared-operand branch with the inner `or` commuted. -/
public def xorXorCommutedOrSharedRight : Pattern OpCode :=
  xorXorOrSharedPattern true false true

public theorem xorXorCommutedOrSharedRight_valid :
    Pattern.Valid xorXorCommutedOrSharedRight :=
  xorXorOrSharedPattern_valid true false true

/-- Second shared-operand branch with the root `xor` commuted. -/
public def xorOrSharedRightXor : Pattern OpCode :=
  xorXorOrSharedPattern true true false

public theorem xorOrSharedRightXor_valid : Pattern.Valid xorOrSharedRightXor :=
  xorXorOrSharedPattern_valid true true false

/-- Second shared-operand branch with both commutative operations swapped. -/
public def xorCommutedOrSharedRightXor : Pattern OpCode :=
  xorXorOrSharedPattern true true true

public theorem xorCommutedOrSharedRightXor_valid :
    Pattern.Valid xorCommutedOrSharedRightXor :=
  xorXorOrSharedPattern_valid true true true

end Veir.Passes.InstCombineLLVM.XorXorOrShared
