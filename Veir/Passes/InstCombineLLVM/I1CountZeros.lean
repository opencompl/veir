module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.I1CountZeros

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

@[local cbv_eval] theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t

private def typedConstantProperty (value : Int) (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt value intType))

private def countZerosToNot (opcode : OpCode)
    (predicate : propertiesOf opcode → Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root opcode #[x] #[ty] predicate
      return (ty, x))
    (fun (ty, x) => do
      let minusOneProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        ty (typedConstantProperty (-1))
      let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] minusOneProps
      let xorProps ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[x, minusOne.res[0]!] #[ty] xorProps)
    (fun result => result.res[0]!)

private def countZerosToZero (opcode : OpCode)
    (predicate : propertiesOf opcode → Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun ty => ty.bitwidth = 1)
      let x ← MatchProg.value ty
      let _ ← MatchProg.root opcode #[x] #[ty] predicate
      return (ty, x))
    (fun (ty, _) => do
      let zeroProps ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
        ty (typedConstantProperty 0)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zeroProps)
    (fun result => result.res[0]!)

/-- Scalar i1 specialization of InstCombineCalls.cpp:487-495 for `ctlz(x, false)`. -/
public def ctlzI1ToNot : Pattern OpCode :=
  countZerosToNot (.llvm .intr__ctlz) (fun props => props.is_zero_poison = false)

/-- Scalar i1 specialization of InstCombineCalls.cpp:487-495 for `cttz(x, false)`. -/
public def cttzI1ToNot : Pattern OpCode :=
  countZerosToNot (.llvm .intr__cttz) (fun props => props.is_zero_poison = false)

/-- Scalar i1 specialization of InstCombineCalls.cpp:487-495 for `ctlz(x, true)`. -/
public def ctlzI1ToZero : Pattern OpCode :=
  countZerosToZero (.llvm .intr__ctlz) (fun props => props.is_zero_poison = true)

/-- Scalar i1 specialization of InstCombineCalls.cpp:487-495 for `cttz(x, true)`. -/
public def cttzI1ToZero : Pattern OpCode :=
  countZerosToZero (.llvm .intr__cttz) (fun props => props.is_zero_poison = true)

public theorem ctlzI1ToNot_valid : Pattern.Valid ctlzI1ToNot := by
  simp only [ctlzI1ToNot, countZerosToNot]
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
  rintro type ⟨w, signedness⟩ hType hWidth
  subst type
  change w = 1 at hWidth
  subst w
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = false := hFlag
  obtain rfl := (ctlz_iff _ _ _ _).mp hSource
  rw [hFlag']
  simp [typedConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int 1 (.val (BitVec.ofInt 1 (-1))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg
      (fun z => RuntimeValue.int 1 (.val z))
      (ofInt_normalizeValue { bitwidth := 1, signedness := signedness } (-1)).symm
  refine ⟨.int 1 (LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1)))),
    (xor_iff _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1,
    (LLVM.Int.ctlz x false).cast h ⊒ LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1)))
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, i1_ctlz_false_eq_not] using
    (isRefinedBy_refl (LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1)))))

public theorem cttzI1ToNot_valid : Pattern.Valid cttzI1ToNot := by
  simp only [cttzI1ToNot, countZerosToNot]
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
  rintro type ⟨w, signedness⟩ hType hWidth
  subst type
  change w = 1 at hWidth
  subst w
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = false := hFlag
  obtain rfl := (cttz_iff _ _ _ _).mp hSource
  rw [hFlag']
  simp [typedConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int 1 (.val (BitVec.ofInt 1 (-1))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg
      (fun z => RuntimeValue.int 1 (.val z))
      (ofInt_normalizeValue { bitwidth := 1, signedness := signedness } (-1)).symm
  refine ⟨.int 1 (LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1)))),
    (xor_iff _ _ _ _).mpr rfl, ?_⟩
  change ∃ h : 1 = 1,
    (LLVM.Int.cttz x false).cast h ⊒ LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1)))
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self, i1_cttz_false_eq_not] using
    (isRefinedBy_refl (LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1)))))

public theorem ctlzI1ToZero_valid : Pattern.Valid ctlzI1ToZero := by
  simp only [ctlzI1ToZero, countZerosToZero]
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
  rintro type ⟨w, signedness⟩ hType hWidth
  subst type
  change w = 1 at hWidth
  subst w
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = true := of_decide_eq_true hFlag
  obtain rfl := (ctlz_iff _ _ _ _).mp hSource
  rw [hFlag']
  simp [typedConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int 1 (.val (BitVec.ofInt 1 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg
      (fun z => RuntimeValue.int 1 (.val z))
      (ofInt_normalizeValue { bitwidth := 1, signedness := signedness } 0).symm
  change ∃ h : 1 = 1, (LLVM.Int.ctlz x true).cast h ⊒ .val (BitVec.ofInt 1 0)
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using i1_ctlz_true_refines_zero x

public theorem cttzI1ToZero_valid : Pattern.Valid cttzI1ToZero := by
  simp only [cttzI1ToZero, countZerosToZero]
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
  rintro type ⟨w, signedness⟩ hType hWidth
  subst type
  change w = 1 at hWidth
  subst w
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro props source hFlag hSource
  have hFlag' : props.is_zero_poison = true := of_decide_eq_true hFlag
  obtain rfl := (cttz_iff _ _ _ _).mp hSource
  rw [hFlag']
  simp [typedConstantProperty, IsTypeAttr.cast?_of]
  refine ⟨.int 1 (.val (BitVec.ofInt 1 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg
      (fun z => RuntimeValue.int 1 (.val z))
      (ofInt_normalizeValue { bitwidth := 1, signedness := signedness } 0).symm
  change ∃ h : 1 = 1, (LLVM.Int.cttz x true).cast h ⊒ .val (BitVec.ofInt 1 0)
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using i1_cttz_true_refines_zero x

end Veir.Passes.InstCombineLLVM.I1CountZeros
